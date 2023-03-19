
theorem wl-section-boot
  let wph: wff ph
  assume wl-section-boot.hyp: |- ph


  assert |- ph

  proof
    wl-section-boot.hyp
end
