include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "rpregt0.mm"
include "gt0ne0.mm"
include "syl.mm"

theorem rpne0
  let cA: class A


  assert |- ( A e. RR+ -> A =/= 0 )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    cA
    cc0
    wne
    cA
    rpregt0
    cA
    gt0ne0
    syl
end
