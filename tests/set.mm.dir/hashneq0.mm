include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "c0.mm"
include "cn0.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "hashnn0pnf.mm"
include "cr.mm"
include "cle.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "ne0gt0.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "breq2.mm"
include "neeq1.mm"
include "0ltpnf.mm"
include "0re.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "necomi.mm"
include "2th.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "jaoi.mm"
include "syl.mm"
include "hasheq0.mm"
include "necon3bid.mm"

theorem hashneq0
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( 0 < ( # ` A ) <-> A =/= (/) ) )

  proof
    cA
    cV
    wcel
    #
    cc0
    cA
    chash
    cfv
    #
    clt
    wbr
    #
    @1
    cc0
    wne
    #
    cA
    c0
    wne
    @0
    @1
    cn0
    wcel
    #
    @1
    cpnf
    wceq
    #
    wo
    @2
    @3
    wb
    #
    cA
    cV
    hashnn0pnf
    @4
    @6
    @5
    @4
    @3
    @2
    @4
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @3
    @2
    wb
    @1
    nn0re
    @1
    nn0ge0
    @1
    ne0gt0
    syl2anc
    bicomd
    @5
    @2
    cc0
    cpnf
    clt
    wbr
    #
    @3
    @1
    cpnf
    cc0
    clt
    breq2
    @5
    @3
    cpnf
    cc0
    wne
    #
    @7
    @1
    cpnf
    cc0
    neeq1
    @7
    @8
    0ltpnf
    cc0
    cpnf
    cc0
    cr
    wcel
    cc0
    cpnf
    wne
    0re
    cc0
    renepnf
    ax-mp
    necomi
    2th
    syl6rbbr
    bitrd
    jaoi
    syl
    @0
    @1
    cc0
    cA
    c0
    cA
    cV
    hasheq0
    necon3bid
    bitrd
end
