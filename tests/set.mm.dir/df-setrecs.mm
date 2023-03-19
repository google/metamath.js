
axiom df-setrecs
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  assert |- setrecs ( F ) = U. { y | A. z ( A. w ( w C_ y -> ( w C_ z -> ( F ` w ) C_ z ) ) -> y C_ z ) }
end
