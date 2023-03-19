include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "xrleid.mm"
include "syl.mm"

theorem xrleidd
  let wph: wff ph
  let cA: class A
  assume xrleidd.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> A <_ A )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cA
    cle
    wbr
    xrleidd.1
    cA
    xrleid
    syl
end
