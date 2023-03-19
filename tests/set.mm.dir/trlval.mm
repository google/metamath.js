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
include "cmpt.mm"
include "trlset.mm"
include "fveq1d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem trlval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
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
  disjoint p x
  disjoint K p
  disjoint K x
  disjoint W p
  disjoint W x
  disjoint F p
  disjoint F x
  disjoint k p
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint .\/ k
  disjoint f k
  disjoint f p
  disjoint f w
  disjoint f x
  disjoint K f
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
  disjoint T f
  disjoint T w
  disjoint W f
  disjoint W w
  disjoint A f
  disjoint B f
  disjoint F f
  disjoint .\/ f
  disjoint .<_ f
  disjoint ./\ f
  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T ) -> ( R ` F ) = ( iota_ x e. B A. p e. A ( -. p .<_ W -> x = ( ( p .\/ ( F ` p ) ) ./\ W ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    cF
    cR
    cfv
    cF
    vf
    cT
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vx
    cv
    #
    @1
    @1
    vf
    cv
    #
    cfv
    #
    c.or
    co
    #
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
    cfv
    @2
    @3
    @1
    @1
    cF
    cfv
    #
    c.or
    co
    #
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
    @0
    cF
    cR
    @12
    vx
    cA
    cB
    cV
    cR
    cT
    vf
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vp
    trlset.b
    trlset.l
    trlset.j
    trlset.m
    trlset.a
    trlset.h
    trlset.t
    trlset.r
    trlset
    fveq1d
    vf
    cF
    @11
    @19
    cT
    @12
    @4
    cF
    wceq
    #
    @10
    @18
    vx
    cB
    @20
    @9
    @17
    vp
    cA
    @20
    @8
    @16
    @2
    @20
    @7
    @15
    @3
    @20
    @6
    @14
    cW
    c.an
    @20
    @5
    @13
    @1
    c.or
    @1
    @4
    cF
    fveq1
    oveq2d
    oveq1d
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    @12
    eqid
    @18
    vx
    cB
    riotaex
    fvmpt
    sylan9eq
end
