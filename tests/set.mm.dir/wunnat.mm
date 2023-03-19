include "cfunc.mm"
include "co.mm"
include "cxp.mm"
include "chom.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "cbs.mm"
include "cmap.mm"
include "cpw.mm"
include "cnat.mm"
include "wunfunc.mm"
include "wunxp.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "wunstr.mm"
include "wunrn.mm"
include "wununi.mm"
include "df-base.mm"
include "wunmap.mm"
include "wunpw.mm"
include "wf.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wral.mm"
include "cixp.mm"
include "crab.mm"
include "csb.mm"
include "wcel.mm"
include "cvv.mm"
include "fvex.mm"
include "wsbc.mm"
include "wss.mm"
include "ssrab2.mm"
include "ovssunirn.mm"
include "rgenw.mm"
include "ss2ixp.mm"
include "ax-mp.mm"
include "rnex.mm"
include "uniex.mm"
include "ixpconst.mm"
include "sseqtri.mm"
include "sstri.mm"
include "ovex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "sbcth.mm"
include "sbcel1g.mm"
include "mpbid.mm"
include "rgen2w.mm"
include "eqid.mm"
include "natfval.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "a1i.mm"
include "wunf.mm"

theorem wunnat
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wunnat.1: |- ( ph -> U e. WUni )
  assume wunnat.2: |- ( ph -> C e. U )
  assume wunnat.3: |- ( ph -> D e. U )


  assert |- ( ph -> ( C Nat D ) e. U )

  proof
    wph
    cC
    cD
    cfunc
    co
    #
    @0
    cxp
    #
    cD
    chom
    cfv
    #
    crn
    #
    cuni
    #
    cC
    cbs
    cfv
    #
    cmap
    co
    #
    cpw
    #
    cU
    cC
    cD
    cnat
    co
    #
    wunnat.1
    wph
    @0
    @0
    cU
    wunnat.1
    wph
    cC
    cD
    cU
    wunnat.1
    wunnat.2
    wunnat.3
    wunfunc
    #
    @9
    wunxp
    wph
    @6
    cU
    wunnat.1
    wph
    @4
    @5
    cU
    wunnat.1
    wph
    @3
    cU
    wunnat.1
    wph
    @2
    cU
    wunnat.1
    wph
    cD
    cU
    chom
    c1
    c4
    cdc
    df-hom
    wunnat.1
    wunnat.3
    wunstr
    wunrn
    wununi
    wph
    cC
    cU
    cbs
    c1
    df-base
    wunnat.1
    wunnat.2
    wunstr
    wunmap
    wunpw
    @1
    @7
    @8
    wf
    #
    wph
    vr
    vf
    cv
    #
    c1st
    cfv
    #
    vs
    vg
    cv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    va
    cv
    #
    cfv
    vz
    cv
    #
    vx
    cv
    #
    @15
    @11
    c2nd
    cfv
    co
    cfv
    @18
    vr
    cv
    #
    cfv
    #
    @15
    @19
    cfv
    cop
    @15
    vs
    cv
    #
    cfv
    #
    cD
    cco
    cfv
    #
    co
    co
    @17
    @18
    @15
    @13
    c2nd
    cfv
    co
    cfv
    @18
    @16
    cfv
    @20
    @18
    @21
    cfv
    #
    cop
    @22
    @23
    co
    co
    wceq
    vz
    @18
    @15
    cC
    chom
    cfv
    #
    co
    wral
    vy
    @5
    wral
    vx
    @5
    wral
    #
    va
    vx
    @5
    @20
    @24
    @2
    co
    #
    cixp
    #
    crab
    #
    csb
    #
    csb
    #
    @7
    wcel
    #
    vg
    @0
    wral
    vf
    @0
    wral
    @10
    @32
    vf
    vg
    @0
    @0
    @12
    cvv
    wcel
    #
    @32
    @11
    c1st
    fvex
    @33
    @30
    @7
    wcel
    #
    vr
    @12
    wsbc
    @32
    @34
    vr
    @12
    cvv
    @14
    cvv
    wcel
    #
    @34
    @13
    c1st
    fvex
    @35
    @29
    @7
    wcel
    #
    vs
    @14
    wsbc
    @34
    @36
    vs
    @14
    cvv
    @36
    @29
    @6
    wss
    @29
    @28
    @6
    @26
    va
    @28
    ssrab2
    @28
    vx
    @5
    @4
    cixp
    #
    @6
    @27
    @4
    wss
    #
    vx
    @5
    wral
    @28
    @37
    wss
    @38
    vx
    @5
    @2
    @20
    @24
    ovssunirn
    rgenw
    vx
    @5
    @27
    @4
    ss2ixp
    ax-mp
    vx
    @5
    @4
    cC
    cbs
    fvex
    @3
    @2
    cD
    chom
    fvex
    rnex
    uniex
    ixpconst
    sseqtri
    sstri
    @29
    @6
    @4
    @5
    cmap
    ovex
    elpw2
    mpbir
    sbcth
    vs
    @14
    @29
    @7
    cvv
    sbcel1g
    mpbid
    ax-mp
    sbcth
    vr
    @12
    @30
    @7
    cvv
    sbcel1g
    mpbid
    ax-mp
    rgen2w
    vf
    vg
    @0
    @0
    @31
    @7
    @8
    vx
    vy
    @5
    cC
    cD
    @23
    vf
    vg
    vz
    @25
    @2
    @8
    vs
    vr
    va
    @8
    eqid
    @5
    eqid
    @25
    eqid
    @2
    eqid
    @23
    eqid
    natfval
    fmpt2
    mpbi
    a1i
    wunf
end
