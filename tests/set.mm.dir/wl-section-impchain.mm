
theorem wl-section-impchain
  let wph: wff ph
  assume wl-section-impchain.hyp: |- ph


  assert |- ph

  proof
    wl-section-impchain.hyp
end
