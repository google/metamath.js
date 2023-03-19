include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "wne.mm"
include "cmee.mm"
include "cfv.mm"
include "co.mm"
include "cp0.mm"
include "wceq.mm"
include "wbr.mm"
include "cal.mm"
include "wb.mm"
include "simp13.mm"
include "cvlatl.mm"
include "syl.mm"
include "eqid.mm"
include "atnem0.mm"
include "syld3an1.mm"
include "cbs.mm"
include "atbase.mm"
include "cvlcvrp.mm"
include "syl3an2.mm"
include "bitrd.mm"

theorem cvlatcvr1
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  assume cvlatcvr1.j: |- .\/ = ( join ` K )
  assume cvlatcvr1.c: |- C = ( <o ` K )
  assume cvlatcvr1.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ P e. A /\ Q e. A ) -> ( P =/= Q <-> P C ( P .\/ Q ) ) )

  proof
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    clc
    wcel
    #
    w3a
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
    cP
    cQ
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    #
    cP
    cP
    cQ
    c.or
    co
    cC
    wbr
    #
    cK
    cal
    wcel
    #
    @4
    @3
    @5
    @7
    @10
    wb
    @6
    @2
    @12
    @0
    @1
    @2
    @4
    @5
    simp13
    cK
    cvlatl
    syl
    cA
    cP
    cQ
    cK
    @8
    @9
    @8
    eqid
    #
    @9
    eqid
    #
    cvlatcvr1.a
    atnem0
    syld3an1
    @4
    @3
    cP
    cK
    cbs
    cfv
    #
    wcel
    @5
    @10
    @11
    wb
    cA
    @15
    cP
    cK
    @15
    eqid
    #
    cvlatcvr1.a
    atbase
    cA
    @15
    cC
    cQ
    c.or
    cK
    @8
    cP
    @9
    @16
    cvlatcvr1.j
    @13
    @14
    cvlatcvr1.c
    cvlatcvr1.a
    cvlcvrp
    syl3an2
    bitrd
end
