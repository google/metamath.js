
axiom df-rab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- { x e. A | ph } = { x | ( x e. A /\ ph ) }
end
