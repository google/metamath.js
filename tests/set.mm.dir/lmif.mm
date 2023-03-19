include "wf.mm"
include "cv.mm"
include "cmid.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cstrkg.mm"
include "adantr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "crn.mm"
include "simpr.mm"
include "lmieu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "clmi.mm"
include "cvv.mm"
include "clng.mm"
include "cbs.mm"
include "df-lmi.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "orbi1d.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnexg.mm"
include "mptexg.mm"
include "mp2b.mm"
include "fvmptd.mm"
include "eleq2.mm"
include "breq1.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "syl5eq.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem lmif
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )


  assert |- ( ph -> M : P --> P )

  proof
    wph
    cP
    cP
    cM
    wf
    cP
    cP
    va
    cP
    va
    cv
    #
    vb
    cv
    #
    cG
    cmid
    cfv
    #
    co
    #
    cD
    wcel
    #
    cD
    @0
    @1
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    @0
    @1
    wceq
    #
    wo
    #
    wa
    #
    vb
    cP
    crio
    #
    cmpt
    #
    wf
    wph
    va
    cP
    @11
    cP
    @12
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @10
    vb
    cP
    wreu
    @11
    cP
    wcel
    @14
    @0
    cD
    cP
    cG
    cI
    cL
    c.mi
    vb
    ismid.p
    ismid.d
    ismid.i
    wph
    cG
    cstrkg
    wcel
    #
    @13
    ismid.g
    adantr
    wph
    cG
    c2
    cstrkgld
    wbr
    @13
    ismid.1
    adantr
    lmif.l
    wph
    cD
    cL
    crn
    #
    wcel
    @13
    lmif.d
    adantr
    wph
    @13
    simpr
    lmieu
    @10
    vb
    cP
    riotacl
    syl
    @12
    eqid
    fmptd
    wph
    cP
    cP
    cM
    @12
    wph
    cM
    cD
    cG
    clmi
    cfv
    #
    cfv
    @12
    lmif.m
    wph
    vd
    cD
    va
    cP
    @3
    vd
    cv
    #
    wcel
    #
    @18
    @5
    @6
    wbr
    #
    @8
    wo
    #
    wa
    #
    vb
    cP
    crio
    #
    cmpt
    #
    @12
    @16
    @17
    cvv
    wph
    vg
    cG
    vd
    vg
    cv
    #
    clng
    cfv
    #
    crn
    #
    va
    @25
    cbs
    cfv
    #
    @0
    @1
    @25
    cmid
    cfv
    #
    co
    #
    @18
    wcel
    #
    @18
    @0
    @1
    @26
    co
    #
    @25
    cperpg
    cfv
    #
    wbr
    #
    @8
    wo
    #
    wa
    #
    vb
    @28
    crio
    #
    cmpt
    #
    cmpt
    #
    vd
    @16
    @24
    cmpt
    #
    cvv
    clmi
    cvv
    clmi
    vg
    cvv
    @39
    cmpt
    wceq
    wph
    vg
    vd
    va
    vb
    df-lmi
    a1i
    @25
    cG
    wceq
    #
    @39
    @40
    wceq
    wph
    @41
    vd
    @27
    @38
    @16
    @24
    @41
    @26
    cL
    @41
    @26
    cG
    clng
    cfv
    #
    cL
    @25
    cG
    clng
    fveq2
    lmif.l
    syl6eqr
    #
    rneqd
    @41
    va
    @28
    @37
    cP
    @23
    @41
    @28
    cG
    cbs
    cfv
    #
    cP
    @25
    cG
    cbs
    fveq2
    ismid.p
    syl6eqr
    #
    @41
    @36
    @22
    vb
    @28
    cP
    @45
    @41
    @31
    @19
    @35
    @21
    @41
    @30
    @3
    @18
    @41
    @29
    @2
    @0
    @1
    @25
    cG
    cmid
    fveq2
    oveqd
    eleq1d
    @41
    @34
    @20
    @8
    @41
    @18
    @18
    @32
    @5
    @33
    @6
    @41
    @18
    eqidd
    @25
    cG
    cperpg
    fveq2
    @41
    @26
    cL
    @0
    @1
    @43
    oveqd
    breq123d
    orbi1d
    anbi12d
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    adantl
    wph
    @15
    cG
    cvv
    wcel
    ismid.g
    cG
    cstrkg
    elex
    syl
    @40
    cvv
    wcel
    #
    wph
    cL
    cvv
    wcel
    @16
    cvv
    wcel
    @46
    cL
    @42
    cvv
    lmif.l
    cG
    clng
    fvex
    eqeltri
    cL
    cvv
    rnexg
    vd
    @16
    @24
    cvv
    mptexg
    mp2b
    a1i
    fvmptd
    @18
    cD
    wceq
    #
    @24
    @12
    wceq
    wph
    @47
    va
    cP
    @23
    @11
    @47
    @22
    @10
    vb
    cP
    @47
    @19
    @4
    @21
    @9
    @18
    cD
    @3
    eleq2
    @47
    @20
    @7
    @8
    @18
    cD
    @5
    @6
    breq1
    orbi1d
    anbi12d
    riotabidv
    mpteq2dv
    adantl
    lmif.d
    @12
    cvv
    wcel
    wph
    va
    cP
    @11
    cP
    @44
    cvv
    ismid.p
    cG
    cbs
    fvex
    eqeltri
    mptex
    a1i
    fvmptd
    syl5eq
    feq1d
    mpbird
end
