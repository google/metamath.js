

axiom df-rab
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  assert |- { x e. A | ph } = { x | ( x e. A /\ ph ) }
end
