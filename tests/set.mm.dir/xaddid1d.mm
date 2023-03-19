include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "xaddid1.mm"
include "syl.mm"

theorem xaddid1d
  let wph: wff ph
  let cA: class A
  assume xaddid1d.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> ( A +e 0 ) = A )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cc0
    cxad
    co
    cA
    wceq
    xaddid1d.1
    cA
    xaddid1
    syl
end
