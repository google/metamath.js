include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "breq1.mm"
include "biimpd.mm"
include "adantl.mm"
include "wb.mm"
include "atcvr0eq.mm"
include "3adant3r1.mm"
include "adantr.mm"
include "sylibd.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "oveq1.mm"
include "breq2d.mm"
include "biimpac.mm"
include "simpr3.mm"
include "hlatjidm.mm"
include "syldan.mm"
include "cal.mm"
include "hlatl.mm"
include "simpr1.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "atcvreq0.mm"
include "syl3anc.mm"
include "sylbid.mm"
include "syl5.mm"
include "expd.mm"
include "impbid.mm"

theorem atcvrj0
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume atcvrj0.b: |- B = ( Base ` K )
  assume atcvrj0.j: |- .\/ = ( join ` K )
  assume atcvrj0.z: |- .0. = ( 0. ` K )
  assume atcvrj0.c: |- C = ( <o ` K )
  assume atcvrj0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) /\ X C ( P .\/ Q ) ) -> ( X = .0. <-> P = Q ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
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
    cX
    cP
    cQ
    c.or
    co
    #
    cC
    wbr
    #
    w3a
    cX
    c.0
    wceq
    #
    cP
    cQ
    wceq
    #
    @0
    @4
    @6
    @7
    @8
    wi
    @0
    @4
    wa
    #
    @7
    @6
    @8
    @9
    @7
    @6
    @8
    wi
    @9
    @7
    wa
    @6
    c.0
    @5
    cC
    wbr
    #
    @8
    @7
    @6
    @10
    wi
    @9
    @7
    @6
    @10
    cX
    c.0
    @5
    cC
    breq1
    biimpd
    adantl
    @9
    @10
    @8
    wb
    #
    @7
    @0
    @2
    @3
    @11
    @1
    cA
    cC
    cP
    cQ
    c.or
    cK
    c.0
    atcvrj0.j
    atcvrj0.z
    atcvrj0.c
    atcvrj0.a
    atcvr0eq
    3adant3r1
    adantr
    sylibd
    ex
    com23
    3impia
    @0
    @4
    @6
    @8
    @7
    wi
    @9
    @6
    @8
    @7
    @6
    @8
    wa
    cX
    cQ
    cQ
    c.or
    co
    #
    cC
    wbr
    #
    @9
    @7
    @8
    @6
    @13
    @8
    @5
    @12
    cX
    cC
    cP
    cQ
    cQ
    c.or
    oveq1
    breq2d
    biimpac
    @9
    @13
    cX
    cQ
    cC
    wbr
    #
    @7
    @9
    @12
    cQ
    cX
    cC
    @0
    @4
    @3
    @12
    cQ
    wceq
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    c.or
    cK
    cQ
    atcvrj0.j
    atcvrj0.a
    hlatjidm
    syldan
    breq2d
    @9
    @14
    @7
    @9
    cK
    cal
    wcel
    #
    @1
    @3
    @14
    @7
    wb
    @0
    @16
    @4
    cK
    hlatl
    adantr
    @0
    @1
    @2
    @3
    simpr1
    @15
    cA
    cB
    cC
    cQ
    cK
    cK
    cple
    cfv
    #
    cX
    c.0
    atcvrj0.b
    @17
    eqid
    atcvrj0.z
    atcvrj0.c
    atcvrj0.a
    atcvreq0
    syl3anc
    biimpd
    sylbid
    syl5
    expd
    3impia
    impbid
end
