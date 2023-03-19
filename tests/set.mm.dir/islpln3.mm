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
include "islpln4.mm"
include "wb.mm"
include "simpll.mm"
include "llnbase.mm"
include "adantl.mm"
include "simplr.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "a1i.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem islpln3
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vp: setvar p
  assume islpln3.b: |- B = ( Base ` K )
  assume islpln3.l: |- .<_ = ( le ` K )
  assume islpln3.j: |- .\/ = ( join ` K )
  assume islpln3.a: |- A = ( Atoms ` K )
  assume islpln3.n: |- N = ( LLines ` K )
  assume islpln3.p: |- P = ( LPlanes ` K )

  disjoint A p
  disjoint p y
  disjoint B p
  disjoint B y
  disjoint K p
  disjoint K y
  disjoint .<_ p
  disjoint N p
  disjoint N y
  disjoint X p
  disjoint X y
  assert |- ( ( K e. HL /\ X e. B ) -> ( X e. P <-> E. y e. N E. p e. A ( -. p .<_ y /\ X = ( y .\/ p ) ) ) )

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
    cP
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
    cN
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
    cN
    wrex
    vy
    chlt
    cB
    @4
    cP
    cK
    cN
    cX
    islpln3.b
    @4
    eqid
    #
    islpln3.n
    islpln3.p
    islpln4
    @2
    @5
    @11
    vy
    cN
    @2
    @3
    cN
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
    cK
    cN
    @3
    islpln3.b
    islpln3.n
    llnbase
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
    islpln3.b
    islpln3.l
    islpln3.j
    @12
    islpln3.a
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
