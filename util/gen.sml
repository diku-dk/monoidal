
fun usage () =
    ( TextIO.output(TextIO.stdErr, "USAGE: gen.exe [-N n]\n")
    ; raise Fail "exiting..."
    )

val gen = Random.newgen()

fun int a b =
    floor (real (b-a) * Random.random gen) + a

fun repeat n f a =
    if n = 0 then a
    else repeat (n-1) f (f a)

fun mk n =
    let val gs = repeat n (fn a =>
                              let val xs = repeat (int 4 50) (fn a => Int.toString (int 1 1300) :: a) nil
                              in String.concatWith "," xs :: a
                              end) nil
    in String.concatWith "|" gs
    end

val N =
    case CommandLine.arguments() of
        [] => 100
      | ["-N",s] => (case Int.fromString s of
                         SOME n => n
                       | NONE => usage())
      | _ => usage()

val () = print (mk N)
