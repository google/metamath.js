
theorem dummylink
  let wph: wff ph
  let wps: wff ps
  assume dummylink.1: |- ph
  assume dummylink.2: |- ps


  assert |- ph

  proof
    dummylink.1
end
