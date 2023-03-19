include "cmpt.mm"
include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cres.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "uztrn2.mm"
include "wss.mm"
include "adantr.mm"
include "ssralv.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "fvres.mm"
include "ad2antll.mm"
include "cvv.mm"
include "simprl.mm"
include "adantrr.mm"
include "resexg.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfral.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralimi.mm"
include "ralbi.mm"
include "3syl.mm"
include "sylibrd.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ralimdv.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cz.mm"
include "ulmf.mm"
include "cdm.mm"
include "fdm.mm"
include "dmmptss.mm"
include "syl6eqssr.mm"
include "uzid.mm"
include "adantl.mm"
include "ssel.mm"
include "eluzel2.mm"
include "eleq2s.mm"
include "syl6.mm"
include "syl5com.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wfn.mm"
include "crn.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "frn.mm"
include "rexlimivw.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "eqidd.mm"
include "ulmcl.mm"
include "ulmscl.mm"
include "ulm2.mm"
include "fmpt.mm"
include "sylibr.mm"
include "elmapi.mm"
include "fssresd.mm"
include "cnex.mm"
include "ssexd.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "fmptd.mm"
include "3imtr4d.mm"

theorem ulmss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cG: class G
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let vz: setvar z
  assume ulmss.z: |- Z = ( ZZ>= ` M )
  assume ulmss.t: |- ( ph -> T C_ S )
  assume ulmss.a: |- ( ( ph /\ x e. Z ) -> A e. W )
  assume ulmss.u: |- ( ph -> ( x e. Z |-> A ) ( ~~>u ` S ) G )

  disjoint T x
  disjoint ph x
  disjoint S x
  disjoint Z x
  disjoint j k
  disjoint j m
  disjoint j r
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k r
  disjoint k z
  disjoint A k
  disjoint m r
  disjoint m z
  disjoint A m
  disjoint r z
  disjoint A r
  disjoint A z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G r
  disjoint G z
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M z
  disjoint j x
  disjoint T j
  disjoint k x
  disjoint T k
  disjoint r x
  disjoint T r
  disjoint x z
  disjoint T z
  disjoint j ph
  disjoint k ph
  disjoint m x
  disjoint m ph
  disjoint ph r
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  disjoint S z
  disjoint Z j
  disjoint Z k
  disjoint Z m
  disjoint Z r
  disjoint Z z
  assert |- ( ph -> ( x e. Z |-> ( A |` T ) ) ( ~~>u ` T ) ( G |` T ) )

  proof
    wph
    vx
    cZ
    cA
    cmpt
    #
    cG
    cS
    culm
    cfv
    wbr
    #
    vx
    cZ
    cA
    cT
    cres
    #
    cmpt
    #
    cG
    cT
    cres
    #
    cT
    culm
    cfv
    wbr
    #
    ulmss.u
    wph
    vz
    cv
    #
    vk
    cv
    #
    @0
    cfv
    #
    cfv
    #
    @6
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    crp
    wral
    @6
    @7
    @3
    cfv
    #
    cfv
    #
    @10
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    vz
    cT
    wral
    #
    vk
    @17
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    crp
    wral
    @1
    @5
    wph
    @19
    @27
    vr
    crp
    wph
    @18
    @26
    vj
    cZ
    wph
    @16
    cZ
    wcel
    #
    wa
    @15
    @25
    vk
    @17
    wph
    @28
    @7
    @17
    wcel
    #
    @15
    @25
    wi
    #
    @28
    @29
    wa
    wph
    @7
    cZ
    wcel
    #
    @30
    cM
    @7
    @16
    cZ
    ulmss.z
    uztrn2
    wph
    @31
    wa
    #
    @15
    @14
    vz
    cT
    wral
    #
    @25
    @32
    cT
    cS
    wss
    #
    @15
    @33
    wi
    wph
    @34
    @31
    ulmss.t
    adantr
    @14
    vz
    cT
    cS
    ssralv
    syl
    @32
    @21
    @9
    wceq
    #
    vz
    cT
    wral
    #
    @24
    @14
    wb
    #
    vz
    cT
    wral
    @25
    @33
    wb
    wph
    @36
    vk
    cZ
    wph
    @6
    vx
    cv
    #
    @3
    cfv
    #
    cfv
    #
    @6
    @38
    @0
    cfv
    #
    cfv
    #
    wceq
    #
    vz
    cT
    wral
    #
    vx
    cZ
    wral
    @36
    vk
    cZ
    wral
    wph
    @43
    vx
    vz
    cZ
    cT
    wph
    @38
    cZ
    wcel
    #
    @6
    cT
    wcel
    #
    wa
    wa
    #
    @6
    @2
    cfv
    #
    @6
    cA
    cfv
    #
    @40
    @42
    @46
    @48
    @49
    wceq
    wph
    @45
    @6
    cT
    cA
    fvres
    ad2antll
    @47
    @6
    @39
    @2
    @47
    @45
    @2
    cvv
    wcel
    #
    @39
    @2
    wceq
    wph
    @45
    @46
    simprl
    #
    @47
    cA
    cW
    wcel
    #
    @50
    wph
    @45
    @52
    @46
    ulmss.a
    adantrr
    #
    cA
    cT
    cW
    resexg
    syl
    vx
    cZ
    @2
    cvv
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    fveq1d
    @47
    @6
    @41
    cA
    @47
    @45
    @52
    @41
    cA
    wceq
    @51
    @53
    vx
    cZ
    cA
    cW
    @0
    @0
    eqid
    #
    fvmpt2
    syl2anc
    fveq1d
    3eqtr4d
    ralrimivva
    @44
    @36
    vx
    vk
    cZ
    @44
    vk
    nfv
    @35
    vx
    vz
    cT
    vx
    cT
    nfcv
    vx
    @21
    @9
    vx
    @6
    @20
    vx
    cZ
    @2
    @7
    nffvmpt1
    vx
    @6
    nfcv
    #
    nffv
    vx
    @6
    @8
    vx
    cZ
    cA
    @7
    nffvmpt1
    @56
    nffv
    nfeq
    nfral
    @38
    @7
    wceq
    #
    @43
    @35
    vz
    cT
    @57
    @40
    @21
    @42
    @9
    @57
    @6
    @39
    @20
    @38
    @7
    @3
    fveq2
    fveq1d
    @57
    @6
    @41
    @8
    @38
    @7
    @0
    fveq2
    fveq1d
    eqeq12d
    ralbidv
    cbvral
    sylib
    r19.21bi
    @35
    @37
    vz
    cT
    @35
    @23
    @12
    @13
    clt
    @35
    @22
    @11
    cabs
    @21
    @9
    @10
    cmin
    oveq1
    fveq2d
    breq1d
    ralimi
    @24
    @14
    vz
    cT
    ralbi
    3syl
    sylibrd
    sylan2
    anassrs
    ralimdva
    reximdva
    ralimdv
    wph
    vr
    vz
    @10
    @9
    cS
    vj
    vk
    @0
    cG
    cM
    cvv
    cZ
    ulmss.z
    wph
    vm
    cv
    #
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    #
    @0
    wf
    #
    vm
    cz
    wrex
    #
    cM
    cz
    wcel
    #
    wph
    @1
    @62
    ulmss.u
    cS
    vm
    @0
    cG
    ulmf
    syl
    #
    wph
    @61
    @63
    vm
    cz
    @61
    @59
    cZ
    wss
    #
    wph
    @58
    cz
    wcel
    #
    wa
    #
    @63
    @61
    @59
    @0
    cdm
    cZ
    @59
    @60
    @0
    fdm
    vx
    cZ
    cA
    @0
    @55
    dmmptss
    syl6eqssr
    @67
    @58
    @59
    wcel
    #
    @65
    @63
    @66
    @68
    wph
    @58
    uzid
    adantl
    @65
    @68
    @58
    cZ
    wcel
    @63
    @59
    cZ
    @58
    ssel
    @63
    @58
    cM
    cuz
    cfv
    cZ
    cM
    @58
    eluzel2
    ulmss.z
    eleq2s
    syl6
    syl5com
    syl5
    rexlimdva
    mpd
    #
    wph
    @0
    cZ
    wfn
    #
    @0
    crn
    @60
    wss
    #
    cZ
    @60
    @0
    wf
    #
    wph
    @52
    vx
    cZ
    wral
    @70
    wph
    @52
    vx
    cZ
    ulmss.a
    ralrimiva
    vx
    cZ
    cA
    @0
    cW
    @55
    fnmpt
    syl
    wph
    @62
    @71
    @64
    @61
    @71
    vm
    cz
    @59
    @60
    @0
    frn
    rexlimivw
    syl
    cZ
    @60
    @0
    df-f
    sylanbrc
    #
    wph
    @31
    @6
    cS
    wcel
    #
    wa
    wa
    @9
    eqidd
    wph
    @74
    wa
    @10
    eqidd
    wph
    @1
    cS
    cc
    cG
    wf
    ulmss.u
    cS
    @0
    cG
    ulmcl
    syl
    #
    wph
    @1
    cS
    cvv
    wcel
    ulmss.u
    cS
    @0
    cG
    ulmscl
    syl
    #
    ulm2
    wph
    vr
    vz
    @10
    @21
    cT
    vj
    vk
    @3
    @4
    cM
    cvv
    cZ
    ulmss.z
    @69
    wph
    vx
    cZ
    @2
    cc
    cT
    cmap
    co
    #
    @3
    wph
    @45
    wa
    #
    @2
    @77
    wcel
    #
    cT
    cc
    @2
    wf
    #
    @78
    cS
    cc
    cT
    cA
    @78
    cA
    @60
    wcel
    #
    cS
    cc
    cA
    wf
    wph
    @81
    vx
    cZ
    wph
    @72
    @81
    vx
    cZ
    wral
    @73
    vx
    cZ
    @60
    cA
    @0
    @55
    fmpt
    sylibr
    r19.21bi
    cA
    cc
    cS
    elmapi
    syl
    wph
    @34
    @45
    ulmss.t
    adantr
    fssresd
    @78
    cc
    cvv
    wcel
    cT
    cvv
    wcel
    #
    @79
    @80
    wb
    cnex
    wph
    @82
    @45
    wph
    cT
    cS
    cvv
    @76
    ulmss.t
    ssexd
    #
    adantr
    cc
    cT
    @2
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    @54
    fmptd
    wph
    @31
    @46
    wa
    wa
    @21
    eqidd
    @46
    @6
    @4
    cfv
    @10
    wceq
    wph
    @6
    cT
    cG
    fvres
    adantl
    wph
    cS
    cc
    cT
    cG
    @75
    ulmss.t
    fssresd
    @83
    ulm2
    3imtr4d
    mpd
end
