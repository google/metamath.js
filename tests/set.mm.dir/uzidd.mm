include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "uzid.mm"
include "syl.mm"

theorem uzidd
  let wph: wff ph
  let cM: class M
  assume uzidd.1: |- ( ph -> M e. ZZ )


  assert |- ( ph -> M e. ( ZZ>= ` M ) )

  proof
    wph
    cM
    cz
    wcel
    cM
    cM
    cuz
    cfv
    wcel
    uzidd.1
    cM
    uzid
    syl
end
