
axiom df-had
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) )
end
