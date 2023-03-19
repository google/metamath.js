include "cnpi.mm"
include "wcel.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "wa.mm"
include "df-ni.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"

theorem elni
  let cA: class A


  assert |- ( A e. N. <-> ( A e. _om /\ A =/= (/) ) )

  proof
    cA
    cnpi
    wcel
    cA
    com
    c0
    csn
    cdif
    #
    wcel
    cA
    com
    wcel
    cA
    c0
    wne
    wa
    cnpi
    @0
    cA
    df-ni
    eleq2i
    cA
    com
    c0
    eldifsn
    bitri
end
