
axiom wif
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert wff if- ( ph , ps , ch )
end
