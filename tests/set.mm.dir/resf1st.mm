include "cresf.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cdm.mm"
include "cres.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cop.mm"
include "resfval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "resex.mm"
include "dmexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "op1stg.mm"
include "sylancr.mm"
include "cxp.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "3eqtrd.mm"

theorem resf1st
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume resf1st.f: |- ( ph -> F e. V )
  assume resf1st.h: |- ( ph -> H e. W )
  assume resf1st.s: |- ( ph -> H Fn ( S X. S ) )


  assert |- ( ph -> ( 1st ` ( F |`f H ) ) = ( ( 1st ` F ) |` S ) )

  proof
    wph
    cF
    cH
    cresf
    co
    #
    c1st
    cfv
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
    vz
    @2
    vz
    cv
    #
    cF
    c2nd
    cfv
    cfv
    @5
    cH
    cfv
    cres
    #
    cmpt
    #
    cop
    #
    c1st
    cfv
    #
    @4
    @1
    cS
    cres
    wph
    @0
    @8
    c1st
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
    @4
    cvv
    wcel
    @7
    cvv
    wcel
    #
    @9
    @4
    wceq
    @1
    @3
    cF
    c1st
    fvex
    resex
    wph
    cH
    cW
    wcel
    @2
    cvv
    wcel
    @10
    resf1st.h
    cH
    cW
    dmexg
    vz
    @2
    @6
    cvv
    mptexg
    3syl
    @4
    @7
    cvv
    cvv
    op1stg
    sylancr
    wph
    @3
    cS
    @1
    wph
    @3
    cS
    cS
    cxp
    #
    cdm
    cS
    wph
    @2
    @11
    wph
    cH
    @11
    wfn
    @2
    @11
    wceq
    resf1st.s
    @11
    cH
    fndm
    syl
    dmeqd
    cS
    dmxpid
    syl6eq
    reseq2d
    3eqtrd
end
