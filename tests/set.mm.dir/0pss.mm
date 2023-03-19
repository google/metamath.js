include "c0.mm"
include "wpss.mm"
include "wne.mm"
include "wss.mm"
include "0ss.mm"
include "df-pss.mm"
include "mpbiran.mm"
include "necom.mm"
include "bitri.mm"

theorem 0pss
  let cA: class A


  assert |- ( (/) C. A <-> A =/= (/) )

  proof
    c0
    cA
    wpss
    #
    c0
    cA
    wne
    #
    cA
    c0
    wne
    @0
    c0
    cA
    wss
    @1
    cA
    0ss
    c0
    cA
    df-pss
    mpbiran
    c0
    cA
    necom
    bitri
end
