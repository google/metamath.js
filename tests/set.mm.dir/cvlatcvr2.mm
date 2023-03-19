include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cvlatcvr1.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp13.mm"
include "cvllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem cvlatcvr2
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  assume cvlatcvr1.j: |- .\/ = ( join ` K )
  assume cvlatcvr1.c: |- C = ( <o ` K )
  assume cvlatcvr1.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ P e. A /\ Q e. A ) -> ( P =/= Q <-> P C ( Q .\/ P ) ) )

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
    cP
    cP
    cQ
    c.or
    co
    #
    cC
    wbr
    cP
    cQ
    cP
    c.or
    co
    #
    cC
    wbr
    cA
    cC
    cP
    cQ
    c.or
    cK
    cvlatcvr1.j
    cvlatcvr1.c
    cvlatcvr1.a
    cvlatcvr1
    @6
    @7
    @8
    cP
    cC
    @6
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @10
    wcel
    #
    @7
    @8
    wceq
    @6
    @2
    @9
    @0
    @1
    @2
    @4
    @5
    simp13
    cK
    cvllat
    syl
    @4
    @3
    @11
    @5
    cA
    @10
    cP
    cK
    @10
    eqid
    #
    cvlatcvr1.a
    atbase
    3ad2ant2
    @5
    @3
    @12
    @4
    cA
    @10
    cQ
    cK
    @13
    cvlatcvr1.a
    atbase
    3ad2ant3
    @10
    c.or
    cK
    cP
    cQ
    @13
    cvlatcvr1.j
    latjcom
    syl3anc
    breq2d
    bitrd
end
