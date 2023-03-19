include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "islvol4.mm"
include "wb.mm"
include "simpll.mm"
include "lplnbase.mm"
include "adantl.mm"
include "simplr.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "a1i.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem islvol3
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vp: setvar p
  assume islvol3.b: |- B = ( Base ` K )
  assume islvol3.l: |- .<_ = ( le ` K )
  assume islvol3.j: |- .\/ = ( join ` K )
  assume islvol3.a: |- A = ( Atoms ` K )
  assume islvol3.p: |- P = ( LPlanes ` K )
  assume islvol3.v: |- V = ( LVols ` K )

  disjoint A p
  disjoint p y
  disjoint B p
  disjoint B y
  disjoint K p
  disjoint K y
  disjoint .<_ p
  disjoint P p
  disjoint P y
  disjoint X p
  disjoint X y
  assert |- ( ( K e. HL /\ X e. B ) -> ( X e. V <-> E. y e. P E. p e. A ( -. p .<_ y /\ X = ( y .\/ p ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    vy
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vy
    cP
    wrex
    vp
    cv
    #
    @3
    c.le
    wbr
    wn
    #
    cX
    @3
    @6
    c.or
    co
    #
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    vy
    cP
    wrex
    vy
    chlt
    cB
    @4
    cP
    cK
    cV
    cX
    islvol3.b
    @4
    eqid
    #
    islvol3.p
    islvol3.v
    islvol4
    @2
    @5
    @11
    vy
    cP
    @2
    @3
    cP
    wcel
    #
    wa
    #
    @5
    @7
    @8
    cX
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    @11
    @14
    @0
    @3
    cB
    wcel
    #
    @1
    @5
    @17
    wb
    @0
    @1
    @13
    simpll
    @13
    @18
    @2
    cB
    cP
    cK
    @3
    islvol3.b
    islvol3.p
    lplnbase
    adantl
    @0
    @1
    @13
    simplr
    cA
    cB
    @4
    c.or
    cK
    c.le
    @3
    cX
    vp
    islvol3.b
    islvol3.l
    islvol3.j
    @12
    islvol3.a
    cvrval3
    syl3anc
    @14
    @16
    @10
    vp
    cA
    @14
    @6
    cA
    wcel
    wa
    #
    @15
    @9
    @7
    @15
    @9
    wb
    @19
    @8
    cX
    eqcom
    a1i
    anbi2d
    rexbidva
    bitrd
    rexbidva
    bitrd
end
