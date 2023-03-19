include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cmnf.mm"
include "wne.mm"
include "hashnn0pnf.mm"
include "cr.mm"
include "wnel.mm"
include "wn.mm"
include "mnfnre.mm"
include "df-nel.mm"
include "nn0re.mm"
include "con3i.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "pnfnemnf.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "syl.mm"

theorem hashnemnf
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( # ` A ) =/= -oo )

  proof
    cA
    cV
    wcel
    cA
    chash
    cfv
    #
    cn0
    wcel
    #
    @0
    cpnf
    wceq
    #
    wo
    @0
    cmnf
    wne
    #
    cA
    cV
    hashnn0pnf
    @1
    @3
    @2
    @1
    @0
    cmnf
    @0
    cmnf
    wceq
    @1
    cmnf
    cn0
    wcel
    #
    cmnf
    cr
    wnel
    #
    @4
    wn
    #
    mnfnre
    @5
    cmnf
    cr
    wcel
    #
    wn
    @6
    cmnf
    cr
    df-nel
    @4
    @7
    cmnf
    nn0re
    con3i
    sylbi
    ax-mp
    @0
    cmnf
    cn0
    eleq1
    mtbiri
    necon2ai
    @2
    @3
    cpnf
    cmnf
    wne
    pnfnemnf
    @0
    cpnf
    cmnf
    neeq1
    mpbiri
    jaoi
    syl
end
