-- | Schema-directed queries over deliberately restricted JSON fragments.
-- This layer adds quoted keys, statically specified records, and arrays of records to
-- monoidal. It constructs no general JSON value or syntax tree.
--
-- JSON-facing quoted keys contain 1--7 ASCII letters, digits, or underscores. No
-- escapes, whitespace, or nested containers are supported. Value syntax and
-- range checks are determined by the user-supplied total field parsers:
-- in particular, nat_try accepts leading zeros and wraps on overflow, so
-- selecting it does not provide strict JSON-number validation.
-- Records must contain at least one known field. Missing fields use supplied
-- defaults, duplicates take the last value, and unknown/malformed fields fail.
-- Empty arrays are valid. Parsing failure is distinct from input filtering.
import "monoidal"

-- | A monoid whose generator consumes bytes.
local module type u8monoid = monoid with i=u8

-- | A field specification: key, total value parser, and missing-field default.
local module type KeyValue = {
  -- | Key type.
  type k
  -- | Parsed value type.
  type v
  -- | Parse a value; malformed input must produce #none.
  module Val : u8monoid with o=opt v
  -- | Key identifying this field.
  val key : k
  -- | Value used when the field is absent.
  val default : v
}

-- | Abstract keys containing at most seven bytes.
local module type Key = {
  type t
  -- | Pack a key constant, asserting that its length is at most seven.
  val pack [n] : [n]u8 -> t
  -- | Compare key contents, including their lengths.
  val equal : t -> t -> bool
  -- | Parse an unquoted key. Reject disallowed bytes and excessive length;
  -- empty keys are valid. Rejected bytes are not silently discarded.
  module parser : {val pred:u8 -> bool} -> u8monoid with o=opt t
}

-- | Internal schema operations. Updates distinguish absent fields from failure.
local module type record_schema = {
  type k
  type v
  type update
  module Values : u8monoid
  val empty : update
  val merge : update -> update -> update
  val finish : update -> v
  val select : k -> Values.o -> opt update
  val contains : k -> bool
  val distinct : bool
}

-- | Public interface for schema-directed JSON queries.
-- Parsers return #none on malformed input and #some on success.
module type monoidal_json = {
  -- | Key constants and equality, without exposing their representation.
  module Key : Key
  -- | Unquoted key parser with a caller-supplied character predicate.
  module packed_key : {val pred:u8 -> bool} ->
    u8monoid with o=opt Key.t
  -- | A quoted key of 1--7 ASCII letters, digits, or underscores; no escapes.
  module quoted_key : u8monoid with o=opt Key.t
  -- | Unsigned decimal integers. Leading zeros are allowed; overflow wraps.
  -- Empty input, signs, and tokens of 64 or more digits fail.
  module nat : u8monoid with o=opt u64
  -- | Signed decimal numbers with at most 18 digits; no exponent notation.
  -- At least one digit is required on each side of a decimal point, if present.
  module number : u8monoid with o=opt f64
  -- | Exactly true or false; #some false is distinct from failure.
  module bool : u8monoid with o=opt bool

  -- | Describe a field using its value type, parser, key, and default.
  module field : (X:{type t}) ->
    (u8monoid with o=opt X.t) ->
    {val key:Key.t val default:X.t} ->
    KeyValue with k=Key.t with v=X.t

  -- | Build a schema inductively, then construct its record parser.
  module Record : {
    -- | Empty schema; the result type is the empty tuple.
    module Zero : record_schema with k=Key.t with v=()
    -- | Prepend a field; results follow schema order as nested tuples.
    module Succ : (A:KeyValue with k=Key.t) ->
      (R:record_schema with k=Key.t) ->
      record_schema with k=Key.t with v=(A.v,R.v)
    -- | Parse a nonempty record. Keys may appear in any order; configured
    -- keys must be distinct. Unknown keys and invalid field values fail.
    module Make : (R:record_schema with k=Key.t) ->
      {type v=R.v
       module body : u8monoid with o=opt v
       include u8monoid with o=opt v
       -- | Project successes from both parser views; preserve #none.
       module with_obs : (F:{type o val obs:R.v -> o}) ->
         {type t
          type v=F.o
          module body : u8monoid with o=opt v
          include u8monoid with t=t with o=opt v}}
  }

  -- | Parse a bracket-enclosed array and aggregate its records directly.
  -- An empty array returns #some (Aggregate.obs Aggregate.ne).
  module array_records :
    (R:{type v
        module body : u8monoid with o=opt v
        include u8monoid with o=opt v}) ->
    (Aggregate:monoid with i=R.v) ->
    u8monoid with o=opt Aggregate.o
}

-- | Abstract short keys. Construction validates the seven-byte bound.
-- The parser's summary is abstract too, so malformed packed words cannot
-- be injected by clients. Equality does not expose the representation.
module Key : Key = {
  type t = u64
  def pack [n] (xs:[n]u8) : t =
    assert (length xs <= 7)
      (u64.i64 (length xs) |
       reduce (|) 0u64
         (map (\i -> u64.u8 xs[i] << u64.i64 (8*(i+1)))
              (iota (length xs))))
  def equal (x:t) (y:t) = x == y
  module parser (P:{val pred:u8 -> bool}) = {
    type t = opt u64
    type i = u8
    type o = opt u64
    def ne : t = #some 0u64
    def gen (c:i) : t =
      if P.pred c then #some (1u64 | (u64.u8 c << 8u64)) else #none
    def op (x:t) (y:t) : t =
      match (x,y)
      case (#some a, #some b) ->
        let n = a & 255u64
        let m = b & 255u64
        in if n + m > 7 then #none
           else #some ((n+m) | (((a >> 8u64) |
                                   ((b >> 8u64) << (8u64*n))) << 8u64))
      case _ -> #none
    def obs (x:t) : o = x
  }
}

-- | A record parser with its body parser available for nesting composition.
-- Keeping the body separate lets the array combinator resolve overloaded
-- commas with parens, without consuming the braces twice.
local module type record_parser = {
  -- | Parsed record value.
  type v
  -- | Parse the fields without their enclosing braces.
  module body : u8monoid with o=opt v
  -- | Parse the complete brace-enclosed record.
  include u8monoid with o=opt v
}

module monoidal_json = {
  module Key = Key
  local module M = monoidal
  local open monoidal

  -- | Parse a bare bounded key (no dictionary lookup). Characters failing
  -- the supplied predicate cause failure, not omission. Empty keys are valid.
  module packed_key = Key.parser
  local module AnyKey = packed_key {def pred (_:u8) = true}

  -- | Natural-number tokens as u64. Lexical validation only: leading zeros
  -- are allowed, value overflow wraps, and 64 or more digits fail. Rejects
  -- empty input, signs (including -0), fractions, and whitespace.
  module nat = M.nat_try u64

  -- | Restricted decimal numbers as f64: -?[0-9]+(\.[0-9]+)?, at most
  -- 18 digits. Leading zeros are allowed; exponents are not supported.
  -- This is not a validator for the full JSON-number grammar.
  module number = M.decimal_try f64

  -- | Exactly the unquoted lowercase tokens true and false. A parsed false
  -- is #some false; malformed tokens are #none. All JSON-layer parsers
  -- return opt, so their public names do not need a _try suffix.
  module bool = M.with_obs AnyKey {
    type o = opt bool
    def true_key = Key.pack "true"
    def false_key = Key.pack "false"
    def obs (x:opt Key.t) : o = match x
      case #some k ->
        if Key.equal k true_key then #some true
        else if Key.equal k false_key then #some false
        else #none
      case #none -> #none
  }

  -- | A field description: unquoted key constant, total value parser, default.
  module field (X:{type t}) (M:u8monoid with o=opt X.t)
               (D:{val key:Key.t val default:X.t}) = {
    type k = Key.t
    type v = X.t
    module Val = M
    def key = D.key
    def default = D.default
  }

  local module Identifier = packed_key {
    def pred (c:u8) = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                     (c >= '0' && c <= '9') || c == '_'
  }
  local module KeyBody = M.with_obs Identifier {
    type o = opt Key.t
    def obs (x:opt Key.t) : o = match x
      case #some k -> if Key.equal k (Key.pack "") then #none else #some k
      case _ -> #none
  }

  -- | Parse surrounding quotes and an unescaped identifier key. The bound
  -- applies to the contents, not to the quotes. Observation returns Key.t.
  module quoted_key = M.enclosed {type t=Key.t} KeyBody {
    def left : u8 = '"'
    def right : u8 = '"'
  }

  module Record = {
    module Zero = {
      type k = Key.t
      type v = ()
      type update = ()
      module Values = {
        type t = ()
        type i = u8
        type o = ()
        def ne = ()
        def op (_:t) (_:t) = ()
        def gen (_:i) = ()
        def obs (_:t) = ()
      }
      def empty = ()
      def merge (_:update) (_:update) = ()
      def finish (_:update) = ()
      def select (_:k) (_:Values.o) : opt update = #none
      def contains (_:k) = false
      def distinct = true
    }

    module Succ (A:KeyValue with k=Key.t) (R:record_schema with k=Key.t) = {
      type k = Key.t
      type v = (A.v,R.v)
      type update = (opt A.v,R.update)
      module Values = M.dup {type i=u8} (M.prod A.Val R.Values)
      def empty : update = (#none,R.empty)
      def merge (x:update) (y:update) : update =
        (match y.0 case #none -> x.0 case z -> z, R.merge x.1 y.1)
      def finish (x:update) : v =
        (match x.0 case #some a -> a case #none -> A.default, R.finish x.1)
      def select (key:k) (values:Values.o) : opt update =
        if Key.equal key A.key then
          match values.0
          case #some a -> #some (#some a,R.empty)
          case #none -> #none
        else match R.select key values.1
          case #some rest -> #some (#none,rest)
          case #none -> #none
      def contains (key:k) = Key.equal key A.key || R.contains key
      def distinct = R.distinct && !R.contains A.key
    }

    module Make (R:record_schema with k=Key.t) = {
      type v = R.v
      local module Pair = M.delim_prod quoted_key R.Values
      local module Field = M.with_gen Pair {
        type i = u8
        def gen (c:u8) : Pair.i = if c == ':' then #Del c else #E c
      }
      local module Fields = {
        type t = opt R.update
        type i = del Field.o
        type o = opt v
        def ne : t = #some R.empty
        def gen (x:i) : t = match x
          case #Del _ -> ne
          case #E (#some (#some key,values)) -> R.select key values
          case _ -> #none
        def op (x:t) (y:t) : t = match (x,y)
          case (#some a,#some b) -> #some (R.merge a b)
          case _ -> #none
        def obs (x:t) : o = match x
          case #some a -> #some (R.finish a)
          case #none -> #none
      }
      local module Chunks = M.chunk Field Fields {def del_ign (_:u8) = false}
      local module Bytes = M.with_gen Chunks {
        type i = u8
        def gen (c:u8) : Chunks.i = if c == ',' then #Del c else #E c
      }
      module body = {
        open Bytes
        def obs (x:t) : o = assert R.distinct (Bytes.obs x)
      }
      local module Enclosed = M.enclosed {type t=v} body {
        def left:u8='{' def right:u8='}'
      }
      local module Complete = {
        open Enclosed
        def obs (x:t) : o = assert R.distinct (Enclosed.obs x)
      }
      open Complete

      -- | Capture both parser views; callers supply only the projection.
      module with_obs (F:{type o val obs:R.v -> o}) = {
        type v = F.o
        local module Project = {
          type o = opt v
          def obs (x:opt R.v) : o = match x
            case #some a -> #some (F.obs a)
            case #none -> #none
        }
        module body = M.with_obs body Project
        open M.with_obs Complete Project
      }
    }
  }

  -- | Parse an array of records, feeding each successful record directly
  -- into Aggregate. Its generator can project/filter inputs before reduction.
  -- Commas inside braces separate fields; outer commas separate records.
  module array_records (R:record_parser) (Aggregate:monoid with i=R.v) = {
    local module Elements = M.separated Aggregate {def delimiter:u8=','}
    local module Objects = M.objects {type t=R.v} {type t=Aggregate.o}
      R.body Elements {def left:u8='{' def right:u8='}'}
    open M.enclosed {type t=Aggregate.o} Objects {def left:u8='[' def right:u8=']'}
  }
}
