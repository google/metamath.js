include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "cardidg.mm"
include "syl.mm"

theorem cardidd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cardidd.1: |- ( ph -> A e. B )


  assert |- ( ph -> ( card ` A ) ~~ A )

  proof
    wph
    cA
    cB
    wcel
    cA
    ccrd
    cfv
    cA
    cen
    wbr
    cardidd.1
    cA
    cB
    cardidg
    syl
end
