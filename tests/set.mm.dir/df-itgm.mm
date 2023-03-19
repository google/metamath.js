
axiom df-itgm
  let vw: setvar w
  let vm: setvar m
  assert |- itgm = ( w e. _V , m e. U. ran measures |-> ( ( ( metUnif ` ( w sitm m ) ) CnExt ( UnifSt ` w ) ) ` ( w sitg m ) ) )
end
