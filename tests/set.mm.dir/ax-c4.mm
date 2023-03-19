
axiom ax-c4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assert |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) )
end
