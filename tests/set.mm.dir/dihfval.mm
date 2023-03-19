include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "cdib.mm"
include "cfv.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cdic.mm"
include "cdvh.mm"
include "clsm.mm"
include "wi.mm"
include "wral.mm"
include "clss.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "cdih.mm"
include "dihffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "breq2.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "notbid.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq12d.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotaeqbidv.mm"
include "ifbieq12d.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dihfval
  let vx: setvar x
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
  let vq: setvar q
  let vk: setvar k
  let vw: setvar w
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
  disjoint q x
  disjoint K q
  disjoint u x
  disjoint K u
  disjoint K x
  disjoint B x
  disjoint S u
  disjoint W q
  disjoint W u
  disjoint W x
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
  disjoint u w
  disjoint w x
  disjoint K w
  disjoint ./\ w
  disjoint .<_ w
  disjoint .\/ w
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint D w
  disjoint .(+) w
  disjoint S w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> I = ( x e. B |-> if ( x .<_ W , ( D ` x ) , ( iota_ u e. S A. q e. A ( ( -. q .<_ W /\ ( q .\/ ( x ./\ W ) ) = x ) -> u = ( ( C ` q ) .(+) ( D ` ( x ./\ W ) ) ) ) ) ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cI
    cW
    vw
    cH
    vx
    cB
    vx
    cv
    #
    vw
    cv
    #
    c.le
    wbr
    #
    @1
    @2
    cK
    cdib
    cfv
    #
    cfv
    #
    cfv
    #
    vq
    cv
    #
    @2
    c.le
    wbr
    #
    wn
    #
    @7
    @1
    @2
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
    @7
    @2
    cK
    cdic
    cfv
    #
    cfv
    #
    cfv
    #
    @10
    @5
    cfv
    #
    @2
    cK
    cdvh
    cfv
    #
    cfv
    #
    clsm
    cfv
    #
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
    @20
    clss
    cfv
    #
    crio
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vx
    cB
    @1
    cW
    c.le
    wbr
    #
    @1
    cD
    cfv
    #
    @7
    cW
    c.le
    wbr
    #
    wn
    #
    @7
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
    @14
    @7
    cC
    cfv
    #
    @36
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
    @0
    cI
    cW
    cK
    cdih
    cfv
    #
    cfv
    @31
    dihval.i
    @0
    cW
    @49
    @30
    vx
    vw
    vu
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cV
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihffval
    fveq1d
    syl5eq
    vw
    cW
    @29
    @48
    cH
    @30
    @2
    cW
    wceq
    #
    vx
    cB
    @28
    @47
    @50
    @3
    @32
    @6
    @27
    @33
    @46
    @2
    cW
    @1
    c.le
    breq2
    @50
    @1
    @5
    cD
    @50
    @5
    cW
    @4
    cfv
    cD
    @2
    cW
    @4
    fveq2
    dihval.d
    syl6eqr
    #
    fveq1d
    @50
    @25
    @45
    vu
    @26
    cS
    @50
    @26
    cU
    clss
    cfv
    cS
    @50
    @20
    cU
    clss
    @50
    @20
    cW
    @19
    cfv
    cU
    @2
    cW
    @19
    fveq2
    dihval.u
    syl6eqr
    #
    fveq2d
    dihval.s
    syl6eqr
    @50
    @24
    @44
    vq
    cA
    @50
    @13
    @39
    @23
    @43
    @50
    @9
    @35
    @12
    @38
    @50
    @8
    @34
    @2
    cW
    @7
    c.le
    breq2
    notbid
    @50
    @11
    @37
    @1
    @50
    @10
    @36
    @7
    c.or
    @2
    cW
    @1
    c.an
    oveq2
    #
    oveq2d
    eqeq1d
    anbi12d
    @50
    @22
    @42
    @14
    @50
    @17
    @40
    @18
    @41
    @21
    c.po
    @50
    @21
    cU
    clsm
    cfv
    c.po
    @50
    @20
    cU
    clsm
    @52
    fveq2d
    dihval.p
    syl6eqr
    @50
    @7
    @16
    cC
    @50
    @16
    cW
    @15
    cfv
    cC
    @2
    cW
    @15
    fveq2
    dihval.c
    syl6eqr
    fveq1d
    @50
    @10
    @36
    @5
    cD
    @51
    @53
    fveq12d
    oveq123d
    eqeq2d
    imbi12d
    ralbidv
    riotaeqbidv
    ifbieq12d
    mpteq2dv
    @30
    eqid
    vx
    cB
    @47
    cB
    cK
    cbs
    cfv
    cvv
    dihval.b
    cK
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    sylan9eq
end
