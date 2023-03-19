include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "dihval.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "anasss.mm"

theorem dihvalc
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  let vq: setvar q
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume dihval.b: |- B = ( Base ` K )
  assume dihval.l: |- .<_ = ( le ` K )
  assume dihval.j: |- .\/ = ( join ` K )
  assume dihval.m: |- ./\ = ( meet ` K )
  assume dihval.a: |- A = ( Atoms ` K )
  assume dihval.h: |- H = ( LHyp ` K )
  assume dihval.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihval.d: |- D = ( ( DIsoB ` K ) ` W )
  assume dihval.c: |- C = ( ( DIsoC ` K ) ` W )
  assume dihval.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihval.s: |- S = ( LSubSp ` U )
  assume dihval.p: |- .(+) = ( LSSum ` U )

  disjoint A q
  disjoint q u
  disjoint K q
  disjoint K u
  disjoint S u
  disjoint W q
  disjoint W u
  disjoint X q
  disjoint X u
  disjoint ./\ k
  disjoint .<_ k
  disjoint .\/ k
  disjoint k q
  disjoint A k
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k u
  disjoint k x
  disjoint K k
  disjoint q w
  disjoint q x
  disjoint u w
  disjoint u x
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint ./\ w
  disjoint .<_ w
  disjoint .\/ w
  disjoint A w
  disjoint B w
  disjoint B x
  disjoint C w
  disjoint D w
  disjoint .(+) w
  disjoint S w
  disjoint W w
  disjoint W x
  disjoint ./\ x
  disjoint .<_ x
  disjoint .\/ x
  disjoint A x
  disjoint C x
  disjoint D x
  disjoint .(+) x
  disjoint S x
  disjoint X x
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> ( I ` X ) = ( iota_ u e. S A. q e. A ( ( -. q .<_ W /\ ( q .\/ ( X ./\ W ) ) = X ) -> u = ( ( C ` q ) .(+) ( D ` ( X ./\ W ) ) ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    #
    cX
    cI
    cfv
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    @5
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    wa
    vu
    cv
    @5
    cC
    cfv
    @6
    cD
    cfv
    c.po
    co
    wceq
    wi
    vq
    cA
    wral
    vu
    cS
    crio
    #
    wceq
    @0
    @1
    wa
    @3
    @4
    @2
    cX
    cD
    cfv
    #
    @7
    cif
    @7
    vu
    cA
    cB
    cC
    cD
    c.po
    cS
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.i
    dihval.d
    dihval.c
    dihval.u
    dihval.s
    dihval.p
    dihval
    @2
    @8
    @7
    iffalse
    sylan9eq
    anasss
end
