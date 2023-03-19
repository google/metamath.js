
theorem wl-impchain-com-1.1
  let wph: wff ph
  let wps: wff ps
  assume wl-impchain-com-1.1.a: |- ( ps -> ph )


  assert |- ( ps -> ph )

  proof
    wl-impchain-com-1.1.a
end
