include "csn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "relsn.mm"
include "dmsnn0.mm"
include "bitri.mm"

theorem relsn2OLD
  let cA: class A
  assume relsn2OLD.1: |- A e. _V


  assert |- ( Rel { A } <-> dom { A } =/= (/) )

  proof
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
    relsn2OLD.1
    relsn
    cA
    dmsnn0
    bitri
end
