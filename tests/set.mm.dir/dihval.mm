include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "dihfval.mm"
include "fveq1d.mm"
include "breq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "riotaex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dihval
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
  assert |- ( ( ( K e. V /\ W e. H ) /\ X e. B ) -> ( I ` X ) = if ( X .<_ W , ( D ` X ) , ( iota_ u e. S A. q e. A ( ( -. q .<_ W /\ ( q .\/ ( X ./\ W ) ) = X ) -> u = ( ( C ` q ) .(+) ( D ` ( X ./\ W ) ) ) ) ) ) )

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
    cX
    cI
    cfv
    cX
    vx
    cB
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    @1
    cD
    cfv
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @4
    @1
    cW
    c.an
    co
    #
    c.or
    co
    #
    @1
    wceq
    #
    wa
    #
    vu
    cv
    #
    @4
    cC
    cfv
    #
    @6
    cD
    cfv
    #
    c.po
    co
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    vu
    cS
    crio
    #
    cif
    #
    cmpt
    #
    cfv
    cX
    cW
    c.le
    wbr
    #
    cX
    cD
    cfv
    #
    @5
    @4
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    @10
    @11
    @22
    cD
    cfv
    #
    c.po
    co
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    vu
    cS
    crio
    #
    cif
    #
    @0
    cX
    cI
    @19
    vx
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
    dihfval
    fveq1d
    vx
    cX
    @18
    @32
    cB
    @19
    @1
    cX
    wceq
    #
    @2
    @20
    @3
    @17
    @21
    @31
    @1
    cX
    cW
    c.le
    breq1
    @1
    cX
    cD
    fveq2
    @33
    @16
    @30
    vu
    cS
    @33
    @15
    @29
    vq
    cA
    @33
    @9
    @25
    @14
    @28
    @33
    @8
    @24
    @5
    @33
    @7
    @23
    @1
    cX
    @33
    @6
    @22
    @4
    c.or
    @1
    cX
    cW
    c.an
    oveq1
    #
    oveq2d
    @33
    id
    eqeq12d
    anbi2d
    @33
    @13
    @27
    @10
    @33
    @12
    @26
    @11
    c.po
    @33
    @6
    @22
    cD
    @34
    fveq2d
    oveq2d
    eqeq2d
    imbi12d
    ralbidv
    riotabidv
    ifbieq12d
    @19
    eqid
    @20
    @21
    @31
    cX
    cD
    fvex
    @30
    vu
    cS
    riotaex
    ifex
    fvmpt
    sylan9eq
end
