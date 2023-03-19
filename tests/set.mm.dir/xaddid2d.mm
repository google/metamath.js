include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "xaddid2.mm"
include "syl.mm"

theorem xaddid2d
  let wph: wff ph
  let cA: class A
  assume xaddid2d.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> ( 0 +e A ) = A )

  proof
    wph
    cA
    cxr
    wcel
    cc0
    cA
    cxad
    co
    cA
    wceq
    xaddid2d.1
    cA
    xaddid2
    syl
end
