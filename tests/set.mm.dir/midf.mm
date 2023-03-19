include "cxp.mm"
include "cmid.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cmir.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wral.mm"
include "wreu.mm"
include "wa.mm"
include "clng.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "mideu.mm"
include "ralrimivva.mm"
include "riotacl.mm"
include "2ralimi.mm"
include "syl.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cbs.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-mid.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "riotaeqbidv.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmptd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem midf
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cL: class L
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )


  assert |- ( ph -> ( midG ` G ) : ( P X. P ) --> P )

  proof
    wph
    cP
    cP
    cxp
    #
    cP
    cG
    cmid
    cfv
    #
    wf
    @0
    cP
    va
    vb
    cP
    cP
    vb
    cv
    #
    va
    cv
    #
    vm
    cv
    #
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vm
    cP
    crio
    #
    cmpt2
    #
    wf
    #
    wph
    @9
    cP
    wcel
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    @11
    wph
    @8
    vm
    cP
    wreu
    #
    vb
    cP
    wral
    va
    cP
    wral
    @13
    wph
    @14
    va
    vb
    cP
    cP
    wph
    @3
    cP
    wcel
    #
    @2
    cP
    wcel
    #
    wa
    #
    wa
    vm
    @3
    @2
    cP
    @5
    cG
    cI
    cG
    clng
    cfv
    #
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @18
    eqid
    wph
    cG
    cstrkg
    wcel
    #
    @17
    ismid.g
    adantr
    @5
    eqid
    wph
    @15
    @16
    simprl
    wph
    @15
    @16
    simprr
    wph
    cG
    c2
    cstrkgld
    wbr
    @17
    ismid.1
    adantr
    mideu
    ralrimivva
    @14
    @12
    va
    vb
    cP
    cP
    @8
    vm
    cP
    riotacl
    2ralimi
    syl
    va
    vb
    cP
    cP
    @9
    cP
    @10
    @10
    eqid
    fmpt2
    sylib
    wph
    @0
    cP
    @1
    @10
    wph
    vg
    cG
    va
    vb
    vg
    cv
    #
    cbs
    cfv
    #
    @21
    @2
    @3
    @4
    @20
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vm
    @21
    crio
    #
    cmpt2
    #
    @10
    cvv
    cmid
    cvv
    cmid
    vg
    cvv
    @27
    cmpt
    wceq
    wph
    vg
    vm
    va
    vb
    df-mid
    a1i
    @20
    cG
    wceq
    #
    @27
    @10
    wceq
    wph
    @28
    va
    vb
    @21
    @21
    @26
    cP
    cP
    @9
    @28
    @21
    cG
    cbs
    cfv
    #
    cP
    @20
    cG
    cbs
    fveq2
    ismid.p
    syl6eqr
    #
    @30
    @28
    @25
    @8
    vm
    @21
    cP
    @30
    @28
    @24
    @7
    @2
    @28
    @3
    @23
    @6
    @28
    @4
    @22
    @5
    @20
    cG
    cmir
    fveq2
    fveq1d
    fveq1d
    eqeq2d
    riotaeqbidv
    mpt2eq123dv
    adantl
    wph
    @19
    cG
    cvv
    wcel
    ismid.g
    cG
    cstrkg
    elex
    syl
    @10
    cvv
    wcel
    wph
    va
    vb
    cP
    cP
    @9
    cP
    @29
    cvv
    ismid.p
    cG
    cbs
    fvex
    eqeltri
    #
    @31
    mpt2ex
    a1i
    fvmptd
    feq1d
    mpbird
end
