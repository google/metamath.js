
axiom df-smblfn
  let vf: setvar f
  let vs: setvar s
  let va: setvar a
  assert |- SMblFn = ( s e. SAlg |-> { f e. ( RR ^pm U. s ) | A. a e. RR ( `' f " ( -oo (,) a ) ) e. ( s |`t dom f ) } )
end
