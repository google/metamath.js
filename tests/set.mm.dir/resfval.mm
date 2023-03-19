include "cvv.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cdm.mm"
include "cres.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cop.mm"
include "cresf.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-resf.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "dmeqd.mm"
include "reseq12d.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "opeq12d.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "opex.mm"
include "ovmpt2d.mm"

theorem resfval
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vh: setvar h
  let vz: setvar z
  let vy: setvar y
  let cG: class G
  let cS: class S
  assume resfval.c: |- ( ph -> F e. V )
  assume resfval.d: |- ( ph -> H e. W )

  disjoint F x
  disjoint H x
  disjoint ph x
  disjoint f h
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint h x
  disjoint h z
  disjoint F h
  disjoint x z
  disjoint F z
  disjoint x y
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint f y
  disjoint H f
  disjoint h y
  disjoint H h
  disjoint H y
  disjoint H z
  disjoint f ph
  disjoint h ph
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( F |`f H ) = <. ( ( 1st ` F ) |` dom dom H ) , ( x e. dom H |-> ( ( ( 2nd ` F ) ` x ) |` ( H ` x ) ) ) >. )

  proof
    wph
    vf
    vh
    cF
    cH
    cvv
    cvv
    vf
    cv
    #
    c1st
    cfv
    #
    vh
    cv
    #
    cdm
    #
    cdm
    #
    cres
    #
    vx
    @3
    vx
    cv
    #
    @0
    c2nd
    cfv
    #
    cfv
    #
    @6
    @2
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    #
    cF
    c1st
    cfv
    #
    cH
    cdm
    #
    cdm
    #
    cres
    #
    vx
    @14
    @6
    cF
    c2nd
    cfv
    #
    cfv
    #
    @6
    cH
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    #
    cresf
    cvv
    cresf
    vf
    vh
    cvv
    cvv
    @12
    cmpt2
    wceq
    wph
    vx
    vf
    vh
    df-resf
    a1i
    wph
    @0
    cF
    wceq
    #
    @2
    cH
    wceq
    #
    wa
    wa
    #
    @5
    @16
    @11
    @21
    @25
    @1
    @13
    @4
    @15
    @25
    @0
    cF
    c1st
    wph
    @23
    @24
    simprl
    #
    fveq2d
    @25
    @3
    @14
    @25
    @2
    cH
    wph
    @23
    @24
    simprr
    #
    dmeqd
    #
    dmeqd
    reseq12d
    @25
    vx
    @3
    @10
    @14
    @20
    @28
    @25
    @8
    @18
    @9
    @19
    @25
    @6
    @7
    @17
    @25
    @0
    cF
    c2nd
    @26
    fveq2d
    fveq1d
    @25
    @6
    @2
    cH
    @27
    fveq1d
    reseq12d
    mpteq12dv
    opeq12d
    wph
    cF
    cV
    wcel
    cF
    cvv
    wcel
    resfval.c
    cF
    cV
    elex
    syl
    wph
    cH
    cW
    wcel
    cH
    cvv
    wcel
    resfval.d
    cH
    cW
    elex
    syl
    @22
    cvv
    wcel
    wph
    @16
    @21
    opex
    a1i
    ovmpt2d
end
