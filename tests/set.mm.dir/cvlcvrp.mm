include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "clat.mm"
include "simp13.mm"
include "cvllat.mm"
include "syl.mm"
include "simp2.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "cal.mm"
include "wb.mm"
include "cvlatl.mm"
include "simp3.mm"
include "eqid.mm"
include "atnle.mm"
include "cvlcvr1.mm"
include "3bitr2d.mm"

theorem cvlcvrp
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume cvlcvrp.b: |- B = ( Base ` K )
  assume cvlcvrp.j: |- .\/ = ( join ` K )
  assume cvlcvrp.m: |- ./\ = ( meet ` K )
  assume cvlcvrp.z: |- .0. = ( 0. ` K )
  assume cvlcvrp.c: |- C = ( <o ` K )
  assume cvlcvrp.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ X e. B /\ P e. A ) -> ( ( X ./\ P ) = .0. <-> X C ( X .\/ P ) ) )

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
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cP
    c.an
    co
    #
    c.0
    wceq
    cP
    cX
    c.an
    co
    #
    c.0
    wceq
    #
    cP
    cX
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    cX
    cX
    cP
    c.or
    co
    cC
    wbr
    @6
    @7
    @8
    c.0
    @6
    cK
    clat
    wcel
    #
    @4
    cP
    cB
    wcel
    #
    @7
    @8
    wceq
    @6
    @2
    @12
    @0
    @1
    @2
    @4
    @5
    simp13
    #
    cK
    cvllat
    syl
    @3
    @4
    @5
    simp2
    #
    @5
    @3
    @13
    @4
    cA
    cB
    cP
    cK
    cvlcvrp.b
    cvlcvrp.a
    atbase
    3ad2ant3
    cB
    cK
    c.an
    cX
    cP
    cvlcvrp.b
    cvlcvrp.m
    latmcom
    syl3anc
    eqeq1d
    @6
    cK
    cal
    wcel
    #
    @5
    @4
    @11
    @9
    wb
    @6
    @2
    @16
    @14
    cK
    cvlatl
    syl
    @3
    @4
    @5
    simp3
    @15
    cA
    cB
    cP
    cK
    @10
    c.an
    cX
    c.0
    cvlcvrp.b
    @10
    eqid
    #
    cvlcvrp.m
    cvlcvrp.z
    cvlcvrp.a
    atnle
    syl3anc
    cA
    cB
    cC
    cP
    c.or
    cK
    @10
    cX
    cvlcvrp.b
    @17
    cvlcvrp.j
    cvlcvrp.c
    cvlcvrp.a
    cvlcvr1
    3bitr2d
end
