include "wcel.mm"
include "cv.mm"
include "cltrn.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "ctrl.mm"
include "trlfset.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "breq2.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "mpteq12i.mm"
include "syl6eqr.mm"
include "sylan9eq.mm"

theorem trlset
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vp: setvar p
  let vk: setvar k
  let vw: setvar w
  assume trlset.b: |- B = ( Base ` K )
  assume trlset.l: |- .<_ = ( le ` K )
  assume trlset.j: |- .\/ = ( join ` K )
  assume trlset.m: |- ./\ = ( meet ` K )
  assume trlset.a: |- A = ( Atoms ` K )
  assume trlset.h: |- H = ( LHyp ` K )
  assume trlset.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlset.r: |- R = ( ( trL ` K ) ` W )

  disjoint A p
  disjoint B x
  disjoint f p
  disjoint f x
  disjoint K f
  disjoint p x
  disjoint K p
  disjoint K x
  disjoint T f
  disjoint W f
  disjoint W p
  disjoint W x
  disjoint k p
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint .\/ k
  disjoint f k
  disjoint f w
  disjoint K k
  disjoint p w
  disjoint w x
  disjoint K w
  disjoint .<_ k
  disjoint ./\ k
  disjoint T k
  disjoint A w
  disjoint B w
  disjoint .\/ w
  disjoint .<_ w
  disjoint ./\ w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. C /\ W e. H ) -> R = ( f e. T |-> ( iota_ x e. B A. p e. A ( -. p .<_ W -> x = ( ( p .\/ ( f ` p ) ) ./\ W ) ) ) ) )

  proof
    cK
    cC
    wcel
    #
    cW
    cH
    wcel
    #
    cR
    cW
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
    @2
    c.le
    wbr
    #
    wn
    #
    vx
    cv
    #
    @5
    @5
    vf
    cv
    cfv
    c.or
    co
    #
    @2
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
    cfv
    #
    vf
    cT
    @5
    cW
    c.le
    wbr
    #
    wn
    #
    @8
    @9
    cW
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
    @0
    cR
    cW
    cK
    ctrl
    cfv
    #
    cfv
    @17
    trlset.r
    @0
    cW
    @26
    @16
    vx
    vw
    cA
    cB
    cC
    vf
    cH
    c.or
    cK
    c.le
    c.an
    vp
    trlset.b
    trlset.l
    trlset.j
    trlset.m
    trlset.a
    trlset.h
    trlfset
    fveq1d
    syl5eq
    @1
    @17
    vf
    cW
    @3
    cfv
    #
    @24
    cmpt
    #
    @25
    vw
    cW
    @15
    @28
    cH
    @16
    @2
    cW
    wceq
    #
    vf
    @4
    @14
    @27
    @24
    @2
    cW
    @3
    fveq2
    @29
    @13
    @23
    vx
    cB
    @29
    @12
    @22
    vp
    cA
    @29
    @7
    @19
    @11
    @21
    @29
    @6
    @18
    @2
    cW
    @5
    c.le
    breq2
    notbid
    @29
    @10
    @20
    @8
    @2
    cW
    @9
    c.an
    oveq2
    eqeq2d
    imbi12d
    ralbidv
    riotabidv
    mpteq12dv
    @16
    eqid
    vf
    @27
    @24
    cW
    @3
    fvex
    mptex
    fvmpt
    vf
    cT
    @24
    @27
    @24
    trlset.t
    @24
    eqid
    mpteq12i
    syl6eqr
    sylan9eq
end
