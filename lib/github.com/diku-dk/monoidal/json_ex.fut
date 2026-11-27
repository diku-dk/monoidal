-- JSON-like array query: quoted ASCII alphanumeric/underscore keys (1--7
-- bytes), no escapes, whitespace, or nested containers. Not full JSON:
-- leading-zero numbers are accepted, and ID arithmetic can wrap.
-- Missing fields default to zero; last duplicate wins; unknown fields fail.
-- nat_try checks ID digits; IDs are assumed to fit in u64 (overflow wraps).
-- IDs of 64 or more digits fail. decimal_try rejects malformed scores.
-- All structure, including outer brackets, is handled in a single reduction.
import "monoidal"
import "monoidal_json"
module M = monoidal
module J = monoidal_json

-- Convert the schema's nested tuple to a named record at observation.
type row = {id:u64,score:f64}
module Record = {
  local module Id = J.field {type t=u64} J.nat {
    def key = J.Key.pack "id"
    def default = 0u64
  }
  local module Score = J.field {type t=f64} J.number {
    def key = J.Key.pack "score"
    def default = 0f64
  }
  local module Fields = J.Record.Succ Id (J.Record.Succ Score J.Record.Zero)
  local module Parsed = J.Record.Make Fields
  open Parsed.with_obs {
    type o = row
    def obs ((id,(score,())):Fields.v) : o = {id,score}
  }
}
module QuotedKey = J.quoted_key

-- Rejected valid records generate the sum's neutral element, zero.
-- Invalid records still fail; separators are checked even for rejected rows.
-- Name the numeric instance to avoid a nightly monomorphisation bug.
module ScoreSum = M.sum f64
module Scores = M.input_filter (M.with_gen ScoreSum {
  type i = Record.v
  def gen (r:i) = r.score
}) {def pred (r:Record.v) = r.id == 5}
module Query = J.array_records Record Scores

def query (xs:[]u8) : opt f64 =
  Query.obs (reduce Query.op Query.ne (map Query.gen xs))

-- Test entry points.
def key_matches (spelling:[]u8) (name:[]u8) : bool =
  match QuotedKey.obs (reduce QuotedKey.op QuotedKey.ne (map QuotedKey.gen spelling))
  case #some k -> Key.equal k (J.Key.pack name)
  case _ -> false

entry main (xs:[]u8) : (bool,f64) =
  match query xs
  case #some s -> (true,s)
  case #none -> (false,0)

-- ==
-- entry: main
-- input { "[{\"id\":5,\"score\":8.1},{\"id\":2,\"score\":2.0},{\"id\":5,\"score\":2.2}]" } output { true 10.3f64 }
-- input { "[]" } output { true 0f64 }
-- input { "[{\"score\":12.75,\"id\":5},{\"id\":5,\"score\":-2.25}]" } output { true 10.5f64 }
-- input { "[{\"id\":2,\"score\":99.5}]" } output { true 0f64 }
-- input { "[{\"id\":2,\"score\":1},{\"id\":3,\"score\":2}]" } output { true 0f64 }
-- input { "[{\"id\":2}{\"id\":3}]" } output { false 0f64 }
-- input { "[{\"id\":2},]" } output { false 0f64 }
-- input { "[{\"id\":2},,{\"id\":3}]" } output { false 0f64 }
-- input { "[{\"id\":5},{\"score\":8.25}]" } output { true 0f64 }
-- input { "[{\"id\":2,\"id\":5,\"score\":9,\"score\":0.5}]" } output { true 0.5f64 }
-- input { "[{\"id\":123456789012345678,\"score\":99},{\"id\":5,\"score\":12.5}]" } output { true 12.5f64 }
-- input { "[{\"id\":5.0,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"id\":-5,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"id\":-0,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"id\":,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"id\":0005,\"score\":1.25}]" } output { true 1.25f64 }
-- input { "[{\"id\":18446744073709551615,\"score\":99},{\"id\":5,\"score\":2.5}]" } output { true 2.5f64 }
-- input { "[{\"id\":5,\"score\":bad}]" } output { false 0f64 }
-- input { "[{\"id\":2,\"score\":bad}]" } output { false 0f64 }
-- input { "[{\"unknown\":5}]" } output { false 0f64 }
-- input { "[{}]" } output { false 0f64 }
-- input { "[,{}]" } output { false 0f64 }
-- input { "[{\"id\":5},]" } output { false 0f64 }
-- input { "[{\"id\":5}{\"score\":2}]" } output { false 0f64 }
-- input { "[{\"id\":5},,{\"score\":2}]" } output { false 0f64 }
-- input { "[{\"id\":5,,\"score\":2}]" } output { false 0f64 }
-- input { "[{\"id\":5,\"score\":2,}]" } output { false 0f64 }
-- input { "[{\"id\"::5}]" } output { false 0f64 }
-- input { "[{\"id\":5]" } output { false 0f64 }
-- input { "[\"id\":5}]" } output { false 0f64 }
-- input { "[{{\"id\":5}}]" } output { false 0f64 }
-- input { "[[{\"id\":5}]]" } output { false 0f64 }
-- input { "{\"id\":5}" } output { false 0f64 }
-- input { "" } output { false 0f64 }
-- input { "[" } output { false 0f64 }
-- input { "[ {\"id\":5}]" } output { false 0f64 }

-- ==
-- entry: main
-- input { "[{id:5,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"id\":5,score:1}]" } output { false 0f64 }
-- input { "[{\"id:5,\"score\":1}]" } output { false 0f64 }
-- input { "[{\"i\"d\":5}]" } output { false 0f64 }
-- input { "[{\"i\\d\":5}]" } output { false 0f64 }
-- input { "[{\"id,score\":5}]" } output { false 0f64 }
-- input { "[{\"id:score\":5}]" } output { false 0f64 }
-- input { "[{\"\":5}]" } output { false 0f64 }
-- input { "[{\"abcdefgh\":5}]" } output { false 0f64 }
