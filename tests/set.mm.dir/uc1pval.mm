include "cuc1p.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "cco1.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "cpl1.mm"
include "c0g.mm"
include "cdg1.mm"
include "cui.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "neeq2d.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-uc1p.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wss.mm"
include "ssrab2.mm"
include "syl5eq.mm"
include "base0.mm"
include "syl5sseq.mm"
include "ss0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem uc1pval
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let vf: setvar f
  let c.0: class .0.
  let vr: setvar r
  let cF: class F
  assume uc1pval.p: |- P = ( Poly1 ` R )
  assume uc1pval.b: |- B = ( Base ` P )
  assume uc1pval.z: |- .0. = ( 0g ` P )
  assume uc1pval.d: |- D = ( deg1 ` R )
  assume uc1pval.c: |- C = ( Unic1p ` R )
  assume uc1pval.u: |- U = ( Unit ` R )

  disjoint B f
  disjoint D f
  disjoint R f
  disjoint U f
  disjoint .0. f
  disjoint B r
  disjoint f r
  disjoint D r
  disjoint F f
  disjoint R r
  disjoint U r
  disjoint .0. r
  assert |- C = { f e. B | ( f =/= .0. /\ ( ( coe1 ` f ) ` ( D ` f ) ) e. U ) }

  proof
    cC
    cR
    cuc1p
    cfv
    #
    vf
    cv
    #
    c.0
    wne
    #
    @1
    cD
    cfv
    #
    @1
    cco1
    cfv
    #
    cfv
    #
    cU
    wcel
    #
    wa
    #
    vf
    cB
    crab
    #
    uc1pval.c
    cR
    cvv
    wcel
    #
    @0
    @8
    wceq
    vr
    cR
    @1
    vr
    cv
    #
    cpl1
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    @1
    @10
    cdg1
    cfv
    #
    cfv
    #
    @4
    cfv
    #
    @10
    cui
    cfv
    #
    wcel
    #
    wa
    #
    vf
    @11
    cbs
    cfv
    #
    crab
    @8
    cvv
    cuc1p
    @10
    cR
    wceq
    #
    @19
    @7
    vf
    @20
    cB
    @21
    @20
    cP
    cbs
    cfv
    #
    cB
    @21
    @11
    cP
    cbs
    @21
    @11
    cR
    cpl1
    cfv
    #
    cP
    @10
    cR
    cpl1
    fveq2
    uc1pval.p
    syl6eqr
    #
    fveq2d
    uc1pval.b
    syl6eqr
    @21
    @13
    @2
    @18
    @6
    @21
    @12
    c.0
    @1
    @21
    @12
    cP
    c0g
    cfv
    c.0
    @21
    @11
    cP
    c0g
    @24
    fveq2d
    uc1pval.z
    syl6eqr
    neeq2d
    @21
    @16
    @5
    @17
    cU
    @21
    @15
    @3
    @4
    @21
    @1
    @14
    cD
    @21
    @14
    cR
    cdg1
    cfv
    cD
    @10
    cR
    cdg1
    fveq2
    uc1pval.d
    syl6eqr
    fveq1d
    fveq2d
    @21
    @17
    cR
    cui
    cfv
    cU
    @10
    cR
    cui
    fveq2
    uc1pval.u
    syl6eqr
    eleq12d
    anbi12d
    rabeqbidv
    vf
    vr
    df-uc1p
    @7
    vf
    cB
    cB
    @22
    cvv
    uc1pval.b
    cP
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    @9
    wn
    #
    @0
    c0
    @8
    cR
    cuc1p
    fvprc
    @25
    @8
    c0
    wss
    @8
    c0
    wceq
    @25
    cB
    @8
    c0
    @7
    vf
    cB
    ssrab2
    @25
    cB
    @22
    c0
    uc1pval.b
    @25
    @22
    c0
    cbs
    cfv
    c0
    @25
    cP
    c0
    cbs
    @25
    cP
    @23
    c0
    uc1pval.p
    cR
    cpl1
    fvprc
    syl5eq
    fveq2d
    base0
    syl6eqr
    syl5eq
    syl5sseq
    @8
    ss0
    syl
    eqtr4d
    pm2.61i
    eqtri
end
