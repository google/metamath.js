include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "cdvh.mm"
include "cld.mm"
include "clk.mm"
include "coch.mm"
include "clfn.mm"
include "cmpt.mm"
include "clcd.mm"
include "lcdfval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "rabeqbidv.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syl.mm"

theorem lcdval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  assume lcdval.h: |- H = ( LHyp ` K )
  assume lcdval.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcdval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdval.f: |- F = ( LFnl ` U )
  assume lcdval.l: |- L = ( LKer ` U )
  assume lcdval.d: |- D = ( LDual ` U )
  assume lcdval.k: |- ( ph -> ( K e. X /\ W e. H ) )

  disjoint K f
  disjoint F f
  disjoint W f
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint K k
  disjoint K w
  disjoint D w
  disjoint F w
  disjoint L w
  disjoint ._|_ w
  disjoint W w
  assert |- ( ph -> C = ( D |`s { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) } ) )

  proof
    wph
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cC
    cD
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
    @3
    wceq
    #
    vf
    cF
    crab
    #
    cress
    co
    #
    wceq
    lcdval.k
    @0
    @1
    cC
    cW
    vw
    cH
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cld
    cfv
    #
    @2
    @11
    clk
    cfv
    #
    cfv
    #
    @9
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @16
    cfv
    #
    @14
    wceq
    #
    vf
    @11
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    cmpt
    #
    cfv
    #
    @8
    @0
    cC
    cW
    cK
    clcd
    cfv
    #
    cfv
    @24
    lcdval.c
    @0
    cW
    @25
    @23
    vw
    vf
    cH
    cK
    cX
    lcdval.h
    lcdfval
    fveq1d
    syl5eq
    vw
    cW
    @22
    @8
    cH
    @23
    @9
    cW
    wceq
    #
    @12
    cD
    @21
    @7
    cress
    @26
    @12
    cU
    cld
    cfv
    cD
    @26
    @11
    cU
    cld
    @26
    @11
    cW
    @10
    cfv
    cU
    @9
    cW
    @10
    fveq2
    lcdval.u
    syl6eqr
    #
    fveq2d
    lcdval.d
    syl6eqr
    @26
    @19
    @6
    vf
    @20
    cF
    @26
    @20
    cU
    clfn
    cfv
    cF
    @26
    @11
    cU
    clfn
    @27
    fveq2d
    lcdval.f
    syl6eqr
    @26
    @18
    @5
    @14
    @3
    @26
    @17
    @4
    @16
    c.pe
    @26
    @16
    cW
    @15
    cfv
    c.pe
    @9
    cW
    @15
    fveq2
    lcdval.o
    syl6eqr
    #
    @26
    @14
    @3
    @16
    c.pe
    @28
    @26
    @2
    @13
    cL
    @26
    @13
    cU
    clk
    cfv
    cL
    @26
    @11
    cU
    clk
    @27
    fveq2d
    lcdval.l
    syl6eqr
    fveq1d
    #
    fveq12d
    fveq12d
    @29
    eqeq12d
    rabeqbidv
    oveq12d
    @23
    eqid
    cD
    @7
    cress
    ovex
    fvmpt
    sylan9eq
    syl
end
