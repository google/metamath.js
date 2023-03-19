include "wcel.mm"
include "wss.mm"
include "lclkrs.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "crab.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "3sstr4i.mm"
include "jctir.mm"

theorem lclkrs2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  assume lclkrs2.h: |- H = ( LHyp ` K )
  assume lclkrs2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrs2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrs2.s: |- S = ( LSubSp ` U )
  assume lclkrs2.f: |- F = ( LFnl ` U )
  assume lclkrs2.l: |- L = ( LKer ` U )
  assume lclkrs2.d: |- D = ( LDual ` U )
  assume lclkrs2.t: |- T = ( LSubSp ` D )
  assume lclkrs2.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lclkrs2.r: |- R = { g e. F | ( ( ._|_ ` ( ._|_ ` ( L ` g ) ) ) = ( L ` g ) /\ ( ._|_ ` ( L ` g ) ) C_ Q ) }
  assume lclkrs2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrs2.q: |- ( ph -> Q e. S )

  disjoint D g
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint L f
  disjoint L g
  disjoint ._|_ f
  disjoint ._|_ g
  disjoint Q g
  disjoint U g
  assert |- ( ph -> ( R e. T /\ R C_ C ) )

  proof
    wph
    cR
    cT
    wcel
    cR
    cC
    wss
    wph
    cR
    cD
    cQ
    cS
    cT
    cU
    vg
    cF
    cH
    cK
    cL
    c.pe
    cW
    lclkrs2.h
    lclkrs2.o
    lclkrs2.u
    lclkrs2.s
    lclkrs2.f
    lclkrs2.l
    lclkrs2.d
    lclkrs2.t
    lclkrs2.r
    lclkrs2.k
    lclkrs2.q
    lclkrs
    vg
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    #
    @2
    cQ
    wss
    #
    wa
    #
    vg
    cF
    crab
    @4
    vg
    cF
    crab
    #
    cR
    cC
    @6
    @4
    vg
    cF
    @6
    @4
    wi
    @0
    cF
    wcel
    @4
    @5
    simpl
    a1i
    ss2rabi
    lclkrs2.r
    cC
    vf
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @9
    wceq
    #
    vf
    cF
    crab
    @7
    lclkrs2.c
    @12
    @4
    vf
    vg
    cF
    vf
    vg
    weq
    #
    @11
    @3
    @9
    @1
    @13
    @10
    @2
    c.pe
    @13
    @9
    @1
    c.pe
    @8
    @0
    cL
    fveq2
    #
    fveq2d
    fveq2d
    @14
    eqeq12d
    cbvrabv
    eqtri
    3sstr4i
    jctir
end
