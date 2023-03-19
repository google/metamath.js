include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "eqid.mm"
include "atcvrj0.mm"
include "3expa.mm"
include "necon3bid.mm"
include "cplt.mm"
include "simpl.mm"
include "simpr1.mm"
include "clat.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr2.mm"
include "atbase.mm"
include "syl.mm"
include "simpr3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "cvrlt.mm"
include "ex.mm"
include "cvrat.mm"
include "expcomd.mm"
include "syld.mm"
include "imp.mm"
include "sylbird.mm"
include "com23.mm"
include "impd.mm"
include "3impia.mm"

theorem cvrat2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cX: class X
  assume cvrat2.b: |- B = ( Base ` K )
  assume cvrat2.j: |- .\/ = ( join ` K )
  assume cvrat2.c: |- C = ( <o ` K )
  assume cvrat2.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) /\ ( P =/= Q /\ X C ( P .\/ Q ) ) ) -> X e. A )

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
    cP
    cQ
    wne
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
    wa
    cX
    cA
    wcel
    #
    @0
    @4
    wa
    #
    @5
    @7
    @8
    @9
    @7
    @5
    @8
    @9
    @7
    @5
    @8
    wi
    @9
    @7
    wa
    #
    @5
    cX
    cK
    cp0
    cfv
    #
    wne
    #
    @8
    @10
    cX
    @11
    cP
    cQ
    @0
    @4
    @7
    cX
    @11
    wceq
    cP
    cQ
    wceq
    wb
    cA
    cB
    cC
    cP
    cQ
    c.or
    cK
    cX
    @11
    cvrat2.b
    cvrat2.j
    @11
    eqid
    #
    cvrat2.c
    cvrat2.a
    atcvrj0
    3expa
    necon3bid
    @9
    @7
    @12
    @8
    wi
    #
    @9
    @7
    cX
    @6
    cK
    cplt
    cfv
    #
    wbr
    #
    @14
    @9
    @0
    @1
    @6
    cB
    wcel
    #
    @7
    @16
    wi
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @9
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @17
    @0
    @18
    @4
    cK
    hllat
    adantr
    @9
    @2
    @19
    @0
    @1
    @2
    @3
    simpr2
    cA
    cB
    cP
    cK
    cvrat2.b
    cvrat2.a
    atbase
    syl
    @9
    @3
    @20
    @0
    @1
    @2
    @3
    simpr3
    cA
    cB
    cQ
    cK
    cvrat2.b
    cvrat2.a
    atbase
    syl
    cB
    c.or
    cK
    cP
    cQ
    cvrat2.b
    cvrat2.j
    latjcl
    syl3anc
    @0
    @1
    @17
    w3a
    @7
    @16
    chlt
    cB
    cC
    @15
    cK
    cX
    @6
    cvrat2.b
    @15
    eqid
    #
    cvrat2.c
    cvrlt
    ex
    syl3anc
    @9
    @12
    @16
    @8
    cA
    cB
    cP
    cQ
    @15
    c.or
    cK
    cX
    @11
    cvrat2.b
    @21
    cvrat2.j
    @13
    cvrat2.a
    cvrat
    expcomd
    syld
    imp
    sylbird
    ex
    com23
    impd
    3impia
end
