include "cresf.mm"
include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cres.mm"
include "df-ov.mm"
include "cv.mm"
include "cdm.mm"
include "cvv.mm"
include "c1st.mm"
include "cmpt.mm"
include "resfval.mm"
include "fveq2d.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "resex.mm"
include "dmexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "op2ndg.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "wa.mm"
include "simpr.mm"
include "syl6eqr.mm"
include "reseq12d.mm"
include "cxp.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "ovex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem resf2nd
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume resf1st.f: |- ( ph -> F e. V )
  assume resf1st.h: |- ( ph -> H e. W )
  assume resf1st.s: |- ( ph -> H Fn ( S X. S ) )
  assume resf2nd.x: |- ( ph -> X e. S )
  assume resf2nd.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( X ( 2nd ` ( F |`f H ) ) Y ) = ( ( X ( 2nd ` F ) Y ) |` ( X H Y ) ) )

  proof
    wph
    cX
    cY
    cF
    cH
    cresf
    co
    #
    c2nd
    cfv
    #
    co
    cX
    cY
    cop
    #
    @1
    cfv
    cX
    cY
    cF
    c2nd
    cfv
    #
    co
    #
    cX
    cY
    cH
    co
    #
    cres
    #
    cX
    cY
    @1
    df-ov
    wph
    vz
    @2
    vz
    cv
    #
    @3
    cfv
    #
    @7
    cH
    cfv
    #
    cres
    #
    @6
    cH
    cdm
    #
    @1
    cvv
    wph
    @1
    cF
    c1st
    cfv
    #
    @11
    cdm
    #
    cres
    #
    vz
    @11
    @10
    cmpt
    #
    cop
    #
    c2nd
    cfv
    #
    @15
    wph
    @0
    @16
    c2nd
    wph
    vz
    cF
    cH
    cV
    cW
    resf1st.f
    resf1st.h
    resfval
    fveq2d
    wph
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    #
    @17
    @15
    wceq
    @12
    @13
    cF
    c1st
    fvex
    resex
    wph
    cH
    cW
    wcel
    @11
    cvv
    wcel
    @18
    resf1st.h
    cH
    cW
    dmexg
    vz
    @11
    @10
    cvv
    mptexg
    3syl
    @14
    @15
    cvv
    cvv
    op2ndg
    sylancr
    eqtrd
    wph
    @7
    @2
    wceq
    #
    wa
    #
    @8
    @4
    @9
    @5
    @20
    @8
    @2
    @3
    cfv
    @4
    @20
    @7
    @2
    @3
    wph
    @19
    simpr
    #
    fveq2d
    cX
    cY
    @3
    df-ov
    syl6eqr
    @20
    @9
    @2
    cH
    cfv
    @5
    @20
    @7
    @2
    cH
    @21
    fveq2d
    cX
    cY
    cH
    df-ov
    syl6eqr
    reseq12d
    wph
    @2
    cS
    cS
    cxp
    #
    @11
    wph
    cX
    cS
    wcel
    cY
    cS
    wcel
    @2
    @22
    wcel
    resf2nd.x
    resf2nd.y
    cX
    cY
    cS
    cS
    opelxpi
    syl2anc
    wph
    cH
    @22
    wfn
    @11
    @22
    wceq
    resf1st.s
    @22
    cH
    fndm
    syl
    eleqtrrd
    @6
    cvv
    wcel
    wph
    @4
    @5
    cX
    cY
    @3
    ovex
    resex
    a1i
    fvmptd
    syl5eq
end
