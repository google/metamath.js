
axiom df-cnext
  let vx: setvar x
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  assert |- CnExt = ( j e. Top , k e. Top |-> ( f e. ( U. k ^pm U. j ) |-> U_ x e. ( ( cls ` j ) ` dom f ) ( { x } X. ( ( k fLimf ( ( ( nei ` j ) ` { x } ) |`t dom f ) ) ` f ) ) ) )
end
