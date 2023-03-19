include "wcel.mm"
include "wss.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "snssi.mm"
include "unss.mm"
include "bicomi.mm"
include "rbaibr.mm"
include "syl.mm"
include "anbi1d.mm"
include "wi.mm"
include "biimpi.mm"
include "expcom.mm"
include "ssun3.mm"
include "a1i.mm"
include "anim12d.mm"
include "pm4.72.mm"
include "sylib.mm"
include "bitrd.mm"
include "wn.mm"
include "cdif.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "disj3.mm"
include "bitr3i.mm"
include "sseq1.mm"
include "sylbi.mm"
include "uncom.mm"
include "sseq2i.mm"
include "ssundif.mm"
include "syl6rbbr.mm"
include "anbi2d.mm"
include "simplbi.mm"
include "biimpd.mm"
include "orcom.mm"
include "syl6bb.mm"
include "pm2.61i.mm"

theorem ssunsn2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( B C_ A /\ A C_ ( C u. { D } ) ) <-> ( ( B C_ A /\ A C_ C ) \/ ( ( B u. { D } ) C_ A /\ A C_ ( C u. { D } ) ) ) )

  proof
    cD
    cA
    wcel
    #
    cB
    cA
    wss
    #
    cA
    cC
    cD
    csn
    #
    cun
    #
    wss
    #
    wa
    #
    @1
    cA
    cC
    wss
    #
    wa
    #
    cB
    @2
    cun
    cA
    wss
    #
    @4
    wa
    #
    wo
    #
    wb
    @0
    @5
    @9
    @10
    @0
    @1
    @8
    @4
    @0
    @2
    cA
    wss
    #
    @1
    @8
    wb
    cD
    cA
    snssi
    #
    @8
    @1
    @11
    @1
    @11
    wa
    #
    @8
    cB
    @2
    cA
    unss
    #
    bicomi
    #
    rbaibr
    syl
    anbi1d
    @0
    @7
    @9
    wi
    @9
    @10
    wb
    @0
    @1
    @8
    @6
    @4
    @0
    @11
    @1
    @8
    wi
    @12
    @1
    @11
    @8
    @13
    @8
    @14
    biimpi
    expcom
    syl
    @6
    @4
    wi
    @0
    cA
    cC
    @2
    ssun3
    a1i
    anim12d
    @7
    @9
    pm4.72
    sylib
    bitrd
    @0
    wn
    #
    @5
    @7
    @10
    @16
    @4
    @6
    @1
    @16
    @6
    cA
    @2
    cdif
    #
    cC
    wss
    #
    @4
    @16
    cA
    @17
    wceq
    #
    @6
    @18
    wb
    @16
    cA
    @2
    cin
    c0
    wceq
    @19
    cA
    cD
    disjsn
    cA
    @2
    disj3
    bitr3i
    cA
    @17
    cC
    sseq1
    sylbi
    @4
    cA
    @2
    cC
    cun
    #
    wss
    @18
    @20
    @3
    cA
    @2
    cC
    uncom
    sseq2i
    cA
    @2
    cC
    ssundif
    bitr3i
    syl6rbbr
    #
    anbi2d
    @16
    @7
    @9
    @7
    wo
    #
    @10
    @16
    @9
    @7
    wi
    @7
    @22
    wb
    @16
    @8
    @1
    @4
    @6
    @8
    @1
    wi
    @16
    @8
    @1
    @11
    @15
    simplbi
    a1i
    @16
    @4
    @6
    @21
    biimpd
    anim12d
    @9
    @7
    pm4.72
    sylib
    @9
    @7
    orcom
    syl6bb
    bitrd
    pm2.61i
end
