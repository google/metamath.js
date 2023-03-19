include "wcel.mm"
include "cvv.mm"
include "cdih.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cdib.mm"
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
include "elex.mm"
include "clh.mm"
include "cbs.mm"
include "cple.mm"
include "cmee.mm"
include "cjn.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "notbid.mm"
include "eqidd.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "riotaeqbidv.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "df-dih.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dihffval
  let vx: setvar x
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let vq: setvar q
  let vk: setvar k
  assume dihval.b: |- B = ( Base ` K )
  assume dihval.l: |- .<_ = ( le ` K )
  assume dihval.j: |- .\/ = ( join ` K )
  assume dihval.m: |- ./\ = ( meet ` K )
  assume dihval.a: |- A = ( Atoms ` K )
  assume dihval.h: |- H = ( LHyp ` K )

  disjoint A q
  disjoint H w
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint K q
  disjoint u w
  disjoint u x
  disjoint K u
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint ./\ k
  disjoint .<_ k
  disjoint .\/ k
  disjoint k q
  disjoint A k
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint k u
  disjoint k x
  disjoint K k
  assert |- ( K e. V -> ( DIsoH ` K ) = ( w e. H |-> ( x e. B |-> if ( x .<_ w , ( ( ( DIsoB ` K ) ` w ) ` x ) , ( iota_ u e. ( LSubSp ` ( ( DVecH ` K ) ` w ) ) A. q e. A ( ( -. q .<_ w /\ ( q .\/ ( x ./\ w ) ) = x ) -> u = ( ( ( ( DIsoC ` K ) ` w ) ` q ) ( LSSum ` ( ( DVecH ` K ) ` w ) ) ( ( ( DIsoB ` K ) ` w ) ` ( x ./\ w ) ) ) ) ) ) ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdih
    cfv
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
    @0
    @1
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
    @1
    c.le
    wbr
    #
    wn
    #
    @6
    @0
    @1
    c.an
    co
    #
    c.or
    co
    #
    @0
    wceq
    #
    wa
    #
    vu
    cv
    #
    @6
    @1
    cK
    cdic
    cfv
    #
    cfv
    #
    cfv
    #
    @9
    @4
    cfv
    #
    @1
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
    @19
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
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    @30
    cbs
    cfv
    #
    @0
    @1
    @30
    cple
    cfv
    #
    wbr
    #
    @0
    @1
    @30
    cdib
    cfv
    #
    cfv
    #
    cfv
    #
    @6
    @1
    @33
    wbr
    #
    wn
    #
    @6
    @0
    @1
    @30
    cmee
    cfv
    #
    co
    #
    @30
    cjn
    cfv
    #
    co
    #
    @0
    wceq
    #
    wa
    #
    @13
    @6
    @1
    @30
    cdic
    cfv
    #
    cfv
    #
    cfv
    #
    @41
    @36
    cfv
    #
    @1
    @30
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
    @30
    catm
    cfv
    #
    wral
    #
    vu
    @51
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
    @29
    cvv
    cdih
    @30
    cK
    wceq
    #
    vw
    @31
    @61
    cH
    @28
    @62
    @31
    cK
    clh
    cfv
    #
    cH
    @30
    cK
    clh
    fveq2
    dihval.h
    syl6eqr
    @62
    vx
    @32
    @60
    cB
    @27
    @62
    @32
    cK
    cbs
    cfv
    cB
    @30
    cK
    cbs
    fveq2
    dihval.b
    syl6eqr
    @62
    @34
    @2
    @37
    @59
    @5
    @26
    @62
    @33
    c.le
    @0
    @1
    @62
    @33
    cK
    cple
    cfv
    c.le
    @30
    cK
    cple
    fveq2
    dihval.l
    syl6eqr
    #
    breqd
    @62
    @0
    @36
    @4
    @62
    @1
    @35
    @3
    @30
    cK
    cdib
    fveq2
    fveq1d
    #
    fveq1d
    @62
    @57
    @24
    vu
    @58
    @25
    @62
    @51
    @19
    clss
    @62
    @1
    @50
    @18
    @30
    cK
    cdvh
    fveq2
    fveq1d
    #
    fveq2d
    @62
    @55
    @23
    vq
    @56
    cA
    @62
    @56
    cK
    catm
    cfv
    cA
    @30
    cK
    catm
    fveq2
    dihval.a
    syl6eqr
    @62
    @45
    @12
    @54
    @22
    @62
    @39
    @8
    @44
    @11
    @62
    @38
    @7
    @62
    @33
    c.le
    @6
    @1
    @64
    breqd
    notbid
    @62
    @43
    @10
    @0
    @62
    @6
    @6
    @41
    @9
    @42
    c.or
    @62
    @42
    cK
    cjn
    cfv
    c.or
    @30
    cK
    cjn
    fveq2
    dihval.j
    syl6eqr
    @62
    @6
    eqidd
    @62
    @40
    c.an
    @0
    @1
    @62
    @40
    cK
    cmee
    cfv
    c.an
    @30
    cK
    cmee
    fveq2
    dihval.m
    syl6eqr
    oveqd
    #
    oveq123d
    eqeq1d
    anbi12d
    @62
    @53
    @21
    @13
    @62
    @48
    @16
    @49
    @17
    @52
    @20
    @62
    @51
    @19
    clsm
    @66
    fveq2d
    @62
    @6
    @47
    @15
    @62
    @1
    @46
    @14
    @30
    cK
    cdic
    fveq2
    fveq1d
    fveq1d
    @62
    @41
    @9
    @36
    @4
    @65
    @67
    fveq12d
    oveq123d
    eqeq2d
    imbi12d
    raleqbidv
    riotaeqbidv
    ifbieq12d
    mpteq12dv
    mpteq12dv
    vx
    vw
    vu
    vk
    vq
    df-dih
    vw
    cH
    @28
    cH
    @63
    cvv
    dihval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
