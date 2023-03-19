include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "ccmp.mm"
include "wa.mm"
include "cms.mm"
include "ctotbnd.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "cdm.mm"
include "wi.mm"
include "cca.mm"
include "wral.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "heibor1lem.mm"
include "expr.mm"
include "ralrimiva.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "simpl.mm"
include "iscmet3.mm"
include "mpbird.mm"
include "cuni.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "cfn.mm"
include "crp.mm"
include "cab.mm"
include "cpw.mm"
include "cin.mm"
include "wss.mm"
include "cxmt.mm"
include "cxr.mm"
include "metxmet.mm"
include "id.mm"
include "rpxr.mm"
include "blopn.mm"
include "syl3an.mm"
include "3com23.mm"
include "3expa.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "adantlr.mm"
include "abssdv.mm"
include "ad2antrr.mm"
include "mopnuni.mm"
include "blcntr.mm"
include "syl3an1.mm"
include "ovex.mm"
include "elabrex.mm"
include "adantl.mm"
include "elunii.mm"
include "syl2anc.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfuni.mm"
include "dfss3f.mm"
include "sylibr.mm"
include "eqsstr3d.mm"
include "unissd.mm"
include "eqssd.mm"
include "eqid.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "rexbii2.mm"
include "sylib.mm"
include "eqcom.mm"
include "eqeq1d.mm"
include "syl5rbb.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "elpwi.mm"
include "ssabral.mm"
include "anim2i.mm"
include "syl6bi.mm"
include "reximdv.mm"
include "mpd.mm"
include "istotbnd.mm"
include "sylanbrc.mm"
include "jca.mm"

theorem heibor1
  let cD: class D
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let vu: setvar u
  let cF: class F
  let vg: setvar g
  let cG: class G
  let wph: wff ph
  let vm: setvar m
  let vv: setvar v
  let vz: setvar z
  let cM: class M
  let cT: class T
  let cB: class B
  let cU: class U
  let wps: wff ps
  let cS: class S
  let cC: class C
  let cK: class K
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( Met ` X ) /\ J e. Comp ) -> ( D e. ( CMet ` X ) /\ D e. ( TotBnd ` X ) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cJ
    ccmp
    wcel
    #
    wa
    #
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    ctotbnd
    cfv
    wcel
    #
    @2
    @3
    cn
    cX
    vx
    cv
    #
    wf
    #
    @5
    cJ
    clm
    cfv
    cdm
    wcel
    #
    wi
    #
    vx
    cD
    cca
    cfv
    #
    wral
    @2
    @8
    vx
    @9
    @2
    @5
    @9
    wcel
    #
    @6
    @7
    @2
    @10
    @6
    wa
    #
    wa
    cD
    @5
    cJ
    cX
    heibor.1
    @0
    @1
    @11
    simpll
    @0
    @1
    @11
    simplr
    @2
    @10
    @6
    simprl
    @2
    @10
    @6
    simprr
    heibor1lem
    expr
    ralrimiva
    @2
    cD
    vx
    cJ
    c1
    cX
    cn
    nnuz
    heibor.1
    @2
    1zzd
    @0
    @1
    simpl
    #
    iscmet3
    mpbird
    @2
    @0
    @5
    cuni
    #
    cX
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vz
    cX
    wrex
    #
    vy
    @5
    wral
    #
    wa
    #
    vx
    cfn
    wrex
    #
    vr
    crp
    wral
    @4
    @12
    @2
    @24
    vr
    crp
    @2
    @17
    crp
    wcel
    #
    wa
    #
    @5
    @21
    vy
    cab
    #
    cpw
    #
    wcel
    #
    cJ
    cuni
    #
    @13
    wceq
    #
    wa
    #
    vx
    cfn
    wrex
    #
    @24
    @26
    @31
    vx
    @28
    cfn
    cin
    #
    wrex
    #
    @33
    @26
    @1
    @27
    cJ
    wss
    @30
    @27
    cuni
    #
    wceq
    @35
    @0
    @1
    @25
    simplr
    @26
    @21
    vy
    cJ
    @0
    @25
    @21
    @15
    cJ
    wcel
    #
    wi
    @1
    @0
    @25
    wa
    #
    @20
    @37
    vz
    cX
    @38
    @16
    cX
    wcel
    #
    wa
    #
    @19
    cJ
    wcel
    #
    @20
    @37
    wi
    @0
    @25
    @39
    @41
    @0
    @39
    @25
    @41
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @39
    @39
    @25
    @17
    cxr
    wcel
    @41
    cD
    cX
    metxmet
    #
    @39
    id
    @17
    rpxr
    cD
    @16
    @17
    cJ
    cX
    heibor.1
    blopn
    syl3an
    3com23
    3expa
    @19
    cJ
    @15
    eleq1a
    syl
    rexlimdva
    adantlr
    abssdv
    #
    @26
    @30
    @36
    @26
    @30
    cX
    @36
    @26
    @42
    cX
    @30
    wceq
    @0
    @42
    @1
    @25
    @43
    ad2antrr
    cD
    cJ
    cX
    heibor.1
    mopnuni
    syl
    #
    @26
    @16
    @36
    wcel
    #
    vz
    cX
    wral
    #
    cX
    @36
    wss
    @0
    @25
    @47
    @1
    @38
    @46
    vz
    cX
    @40
    @16
    @19
    wcel
    #
    @19
    @27
    wcel
    #
    @46
    @0
    @25
    @39
    @48
    @0
    @39
    @25
    @48
    @0
    @42
    @39
    @25
    @48
    @43
    cD
    @16
    @17
    cX
    blcntr
    syl3an1
    3com23
    3expa
    @39
    @49
    @38
    vz
    vy
    cX
    @19
    @16
    @17
    @18
    ovex
    elabrex
    adantl
    @16
    @19
    @27
    elunii
    syl2anc
    ralrimiva
    adantlr
    vz
    cX
    @36
    vz
    cX
    nfcv
    vz
    @27
    @21
    vz
    vy
    @20
    vz
    cX
    nfre1
    nfab
    nfuni
    dfss3f
    sylibr
    eqsstr3d
    @26
    @27
    cJ
    @44
    unissd
    eqssd
    @27
    cJ
    @30
    vx
    @30
    eqid
    cmpcov
    syl3anc
    @31
    @32
    vx
    @34
    cfn
    @5
    @34
    wcel
    #
    @31
    wa
    @5
    cfn
    wcel
    #
    @29
    wa
    #
    @31
    wa
    @51
    @32
    wa
    @50
    @52
    @31
    @50
    @29
    @51
    wa
    @52
    @5
    @28
    cfn
    elin
    @29
    @51
    ancom
    bitri
    anbi1i
    @51
    @29
    @31
    anass
    bitri
    rexbii2
    sylib
    @26
    @32
    @23
    vx
    cfn
    @26
    @32
    @14
    @29
    wa
    #
    @23
    @32
    @31
    @29
    wa
    @26
    @53
    @29
    @31
    ancom
    @26
    @31
    @14
    @29
    @14
    cX
    @13
    wceq
    @26
    @31
    @13
    cX
    eqcom
    @26
    cX
    @30
    @13
    @45
    eqeq1d
    syl5rbb
    anbi1d
    syl5bb
    @29
    @22
    @14
    @29
    @5
    @27
    wss
    @22
    @5
    @27
    elpwi
    @21
    vy
    @5
    ssabral
    sylib
    anim2i
    syl6bi
    reximdv
    mpd
    ralrimiva
    vz
    vx
    cD
    cX
    vy
    vr
    istotbnd
    sylanbrc
    jca
end
