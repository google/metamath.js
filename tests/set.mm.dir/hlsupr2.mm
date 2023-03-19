include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wne.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "eqid.mm"
include "hlsupr.mm"
include "ex.mm"
include "wa.mm"
include "clc.mm"
include "wb.mm"
include "simpl1.mm"
include "hlcvl.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "cvlsupr3.mm"
include "syl13anc.mm"
include "rexbidva.mm"
include "c0.mm"
include "ne0i.mm"
include "3ad2ant2.mm"
include "r19.37zv.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem hlsupr2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let vr: setvar r
  assume hlsupr2.j: |- .\/ = ( join ` K )
  assume hlsupr2.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint K r
  disjoint P r
  disjoint Q r
  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> E. r e. A ( P .\/ r ) = ( Q .\/ r ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cP
    vr
    cv
    #
    c.or
    co
    cQ
    @4
    c.or
    co
    wceq
    #
    vr
    cA
    wrex
    #
    cP
    cQ
    wne
    #
    @4
    cP
    wne
    @4
    cQ
    wne
    @4
    cP
    cQ
    c.or
    co
    cK
    cple
    cfv
    #
    wbr
    w3a
    #
    vr
    cA
    wrex
    #
    wi
    #
    @3
    @7
    @10
    cA
    cP
    cQ
    c.or
    cK
    @8
    vr
    @8
    eqid
    #
    hlsupr2.j
    hlsupr2.a
    hlsupr
    ex
    @3
    @6
    @7
    @9
    wi
    #
    vr
    cA
    wrex
    #
    @11
    @3
    @5
    @13
    vr
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    cK
    clc
    wcel
    #
    @1
    @2
    @15
    @5
    @13
    wb
    @16
    @0
    @17
    @0
    @1
    @2
    @15
    simpl1
    cK
    hlcvl
    syl
    @0
    @1
    @2
    @15
    simpl2
    @0
    @1
    @2
    @15
    simpl3
    @3
    @15
    simpr
    cA
    cP
    cQ
    @4
    c.or
    cK
    @8
    hlsupr2.a
    @12
    hlsupr2.j
    cvlsupr3
    syl13anc
    rexbidva
    @3
    cA
    c0
    wne
    #
    @14
    @11
    wb
    @1
    @0
    @18
    @2
    cA
    cP
    ne0i
    3ad2ant2
    @7
    @9
    vr
    cA
    r19.37zv
    syl
    bitrd
    mpbird
end
