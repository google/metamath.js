
axiom ax-frege58a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( ( ps /\ ch ) -> if- ( ph , ps , ch ) )
end
