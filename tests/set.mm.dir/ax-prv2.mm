
axiom ax-prv2
  let wph: wff ph
  let wps: wff ps
  assert |- ( Prv ( ph -> ps ) -> ( Prv ph -> Prv ps ) )
end
