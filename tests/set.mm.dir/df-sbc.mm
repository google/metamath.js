
axiom df-sbc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( [. A / x ]. ph <-> A e. { x | ph } )
end
