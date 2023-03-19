include "wcel.mm"
include "cvv.mm"
include "ctrl.mm"
include "cfv.mm"
include "cv.mm"
include "cltrn.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "cjn.mm"
include "cmee.mm"
include "catm.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "breqd.mm"
include "notbid.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "df-trl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem trlfset
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let vp: setvar p
  let vk: setvar k
  let cT: class T
  assume trlset.b: |- B = ( Base ` K )
  assume trlset.l: |- .<_ = ( le ` K )
  assume trlset.j: |- .\/ = ( join ` K )
  assume trlset.m: |- ./\ = ( meet ` K )
  assume trlset.a: |- A = ( Atoms ` K )
  assume trlset.h: |- H = ( LHyp ` K )

  disjoint A p
  disjoint B x
  disjoint H w
  disjoint f p
  disjoint f w
  disjoint f x
  disjoint K f
  disjoint p w
  disjoint p x
  disjoint K p
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint k p
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint .\/ k
  disjoint f k
  disjoint K k
  disjoint .<_ k
  disjoint ./\ k
  disjoint T k
  assert |- ( K e. C -> ( trL ` K ) = ( w e. H |-> ( f e. ( ( LTrn ` K ) ` w ) |-> ( iota_ x e. B A. p e. A ( -. p .<_ w -> x = ( ( p .\/ ( f ` p ) ) ./\ w ) ) ) ) ) )

  proof
    cK
    cC
    wcel
    cK
    cvv
    wcel
    cK
    ctrl
    cfv
    vw
    cH
    vf
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    vp
    cv
    #
    @0
    c.le
    wbr
    #
    wn
    #
    vx
    cv
    #
    @3
    @3
    vf
    cv
    cfv
    #
    c.or
    co
    #
    @0
    c.an
    co
    #
    wceq
    #
    wi
    #
    vp
    cA
    wral
    #
    vx
    cB
    crio
    #
    cmpt
    #
    cmpt
    #
    wceq
    cK
    cC
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
    vf
    @0
    @16
    cltrn
    cfv
    #
    cfv
    #
    @3
    @0
    @16
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @6
    @3
    @7
    @16
    cjn
    cfv
    #
    co
    #
    @0
    @16
    cmee
    cfv
    #
    co
    #
    wceq
    #
    wi
    #
    vp
    @16
    catm
    cfv
    #
    wral
    #
    vx
    @16
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    cmpt
    @15
    cvv
    ctrl
    @16
    cK
    wceq
    #
    vw
    @17
    @33
    cH
    @14
    @34
    @17
    cK
    clh
    cfv
    #
    cH
    @16
    cK
    clh
    fveq2
    trlset.h
    syl6eqr
    @34
    vf
    @19
    @32
    @2
    @13
    @34
    @0
    @18
    @1
    @16
    cK
    cltrn
    fveq2
    fveq1d
    @34
    @30
    @12
    vx
    @31
    cB
    @34
    @31
    cK
    cbs
    cfv
    cB
    @16
    cK
    cbs
    fveq2
    trlset.b
    syl6eqr
    @34
    @28
    @11
    vp
    @29
    cA
    @34
    @29
    cK
    catm
    cfv
    cA
    @16
    cK
    catm
    fveq2
    trlset.a
    syl6eqr
    @34
    @22
    @5
    @27
    @10
    @34
    @21
    @4
    @34
    @20
    c.le
    @3
    @0
    @34
    @20
    cK
    cple
    cfv
    c.le
    @16
    cK
    cple
    fveq2
    trlset.l
    syl6eqr
    breqd
    notbid
    @34
    @26
    @9
    @6
    @34
    @24
    @8
    @0
    @0
    @25
    c.an
    @34
    @25
    cK
    cmee
    cfv
    c.an
    @16
    cK
    cmee
    fveq2
    trlset.m
    syl6eqr
    @34
    @23
    c.or
    @3
    @7
    @34
    @23
    cK
    cjn
    cfv
    c.or
    @16
    cK
    cjn
    fveq2
    trlset.j
    syl6eqr
    oveqd
    @34
    @0
    eqidd
    oveq123d
    eqeq2d
    imbi12d
    raleqbidv
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    vx
    vw
    vf
    vk
    vp
    df-trl
    vw
    cH
    @14
    cH
    @35
    cvv
    trlset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
