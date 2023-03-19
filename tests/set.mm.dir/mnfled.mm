include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cle.mm"
include "wbr.mm"
include "mnfle.mm"
include "syl.mm"

theorem mnfled
  let wph: wff ph
  let cA: class A
  assume mnfled.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> -oo <_ A )

  proof
    wph
    cA
    cxr
    wcel
    cmnf
    cA
    cle
    wbr
    mnfled.1
    cA
    mnfle
    syl
end
