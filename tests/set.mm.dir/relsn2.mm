include "wcel.mm"
include "csn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "relsng.mm"
include "dmsnn0.mm"
include "syl6bb.mm"

theorem relsn2
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( Rel { A } <-> dom { A } =/= (/) ) )

  proof
    cA
    cV
    wcel
    cA
    csn
    #
    wrel
    cA
    cvv
    cvv
    cxp
    wcel
    @0
    cdm
    c0
    wne
    cA
    cV
    relsng
    cA
    dmsnn0
    syl6bb
end
