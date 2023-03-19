include "cuz.mm"
include "cfv.mm"
include "uzidd.mm"
include "syl6eleqr.mm"

theorem uzidd2
  let wph: wff ph
  let cM: class M
  let cZ: class Z
  assume uzidd2.1: |- ( ph -> M e. ZZ )
  assume uzidd2.2: |- Z = ( ZZ>= ` M )


  assert |- ( ph -> M e. Z )

  proof
    wph
    cM
    cM
    cuz
    cfv
    cZ
    wph
    cM
    uzidd2.1
    uzidd
    uzidd2.2
    syl6eleqr
end
