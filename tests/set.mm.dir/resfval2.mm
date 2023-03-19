include "cop.mm"
include "cresf.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cdm.mm"
include "cres.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "opex.mm"
include "a1i.mm"
include "resfval.mm"
include "wceq.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "cxp.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "reseq12d.mm"
include "op2ndg.mm"
include "fveq1d.mm"
include "reseq1d.mm"
include "mpteq12dv.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "mpt2mpt.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem resfval2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vz: setvar z
  assume resfval.c: |- ( ph -> F e. V )
  assume resfval.d: |- ( ph -> H e. W )
  assume resfval2.g: |- ( ph -> G e. X )
  assume resfval2.d: |- ( ph -> H Fn ( S X. S ) )

  disjoint F x
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint S x
  disjoint S y
  disjoint f h
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint h x
  disjoint h z
  disjoint F h
  disjoint x z
  disjoint F z
  disjoint y z
  disjoint G z
  disjoint f y
  disjoint H f
  disjoint h y
  disjoint H h
  disjoint H z
  disjoint f ph
  disjoint h ph
  disjoint ph z
  disjoint S z
  assert |- ( ph -> ( <. F , G >. |`f H ) = <. ( F |` S ) , ( x e. S , y e. S |-> ( ( x G y ) |` ( x H y ) ) ) >. )

  proof
    wph
    cF
    cG
    cop
    #
    cH
    cresf
    co
    @0
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
    @0
    c2nd
    cfv
    #
    cfv
    #
    @5
    cH
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    cF
    cS
    cres
    #
    vx
    vy
    cS
    cS
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    @12
    @13
    cH
    co
    #
    cres
    #
    cmpt2
    #
    cop
    wph
    vz
    @0
    cH
    cvv
    cW
    @0
    cvv
    wcel
    wph
    cF
    cG
    opex
    a1i
    resfval.d
    resfval
    wph
    @4
    @11
    @10
    @17
    wph
    @1
    cF
    @3
    cS
    wph
    cF
    cV
    wcel
    #
    cG
    cX
    wcel
    #
    @1
    cF
    wceq
    resfval.c
    resfval2.g
    cF
    cG
    cV
    cX
    op1stg
    syl2anc
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
    @20
    wph
    cH
    @20
    wfn
    @2
    @20
    wceq
    resfval2.d
    @20
    cH
    fndm
    syl
    #
    dmeqd
    cS
    dmxpid
    syl6eq
    reseq12d
    wph
    @10
    vz
    @20
    @5
    cG
    cfv
    #
    @8
    cres
    #
    cmpt
    @17
    wph
    vz
    @2
    @9
    @20
    @23
    @21
    wph
    @7
    @22
    @8
    wph
    @5
    @6
    cG
    wph
    @18
    @19
    @6
    cG
    wceq
    resfval.c
    resfval2.g
    cF
    cG
    cV
    cX
    op2ndg
    syl2anc
    fveq1d
    reseq1d
    mpteq12dv
    vx
    vy
    vz
    cS
    cS
    @23
    @16
    @5
    @12
    @13
    cop
    #
    wceq
    #
    @22
    @14
    @8
    @15
    @25
    @22
    @24
    cG
    cfv
    @14
    @5
    @24
    cG
    fveq2
    @12
    @13
    cG
    df-ov
    syl6eqr
    @25
    @8
    @24
    cH
    cfv
    @15
    @5
    @24
    cH
    fveq2
    @12
    @13
    cH
    df-ov
    syl6eqr
    reseq12d
    mpt2mpt
    syl6eq
    opeq12d
    eqtrd
end
