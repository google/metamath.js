include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cibl.mm"
include "wcel.mm"
include "cuz.mm"
include "wrex.mm"
include "wfn.mm"
include "culm.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "wa.mm"
include "eqidd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "ulmi.mm"
include "r19.2uz.mm"
include "cmpt.mm"
include "ulmcl.mm"
include "adantr.mm"
include "feqmptd.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "adantrr.mm"
include "nncand.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "eqeltrrd.mm"
include "subcld.mm"
include "cmbf.mm"
include "cdm.mm"
include "cvol.mm"
include "cr.mm"
include "cle.mm"
include "cof.mm"
include "cvv.mm"
include "ulmscl.mm"
include "offval2.mm"
include "iblmbf.mm"
include "wss.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "mbfulm.mm"
include "mbfsub.mm"
include "eqid.mm"
include "dmmptd.mm"
include "fveq2d.mm"
include "eqeltrd.mm"
include "1re.mm"
include "wi.mm"
include "abscld.mm"
include "ltle.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "breq1d.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "impr.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "bddibl.mm"
include "syl3anc.mm"
include "iblsub.mm"
include "rexlimddv.mm"

theorem iblulm
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  assume itgulm.z: |- Z = ( ZZ>= ` M )
  assume itgulm.m: |- ( ph -> M e. ZZ )
  assume itgulm.f: |- ( ph -> F : Z --> L^1 )
  assume itgulm.u: |- ( ph -> F ( ~~>u ` S ) G )
  assume itgulm.s: |- ( ph -> ( vol ` S ) e. RR )


  assert |- ( ph -> G e. L^1 )

  proof
    wph
    vx
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @0
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vx
    cS
    wral
    #
    cG
    cibl
    wcel
    vk
    cZ
    wph
    @8
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cZ
    wrex
    @8
    vk
    cZ
    wrex
    wph
    vx
    @4
    @3
    c1
    cS
    vj
    vk
    cF
    cG
    cM
    cZ
    itgulm.z
    itgulm.m
    wph
    cF
    cZ
    wfn
    #
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    wph
    cZ
    cibl
    cF
    wf
    #
    @9
    itgulm.f
    cZ
    cibl
    cF
    ffn
    syl
    itgulm.u
    cS
    cF
    cG
    cZ
    ulmf2
    syl2anc
    #
    wph
    @1
    cZ
    wcel
    #
    @0
    cS
    wcel
    #
    wa
    wa
    @3
    eqidd
    wph
    @15
    wa
    @4
    eqidd
    itgulm.u
    c1
    crp
    wcel
    wph
    1rp
    a1i
    ulmi
    @8
    vj
    vk
    cM
    cZ
    itgulm.z
    r19.2uz
    syl
    wph
    @14
    @8
    wa
    #
    wa
    #
    cG
    vz
    cS
    vz
    cv
    #
    @2
    cfv
    #
    @19
    @18
    cG
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    #
    cibl
    @17
    cG
    vz
    cS
    @20
    cmpt
    @23
    @17
    vz
    cS
    cc
    cG
    wph
    cS
    cc
    cG
    wf
    #
    @16
    wph
    @10
    @24
    itgulm.u
    cS
    cF
    cG
    ulmcl
    syl
    #
    adantr
    #
    feqmptd
    #
    @17
    vz
    cS
    @22
    @20
    @17
    @18
    cS
    wcel
    wa
    #
    @19
    @20
    @17
    cS
    cc
    @18
    @2
    wph
    @14
    cS
    cc
    @2
    wf
    #
    @8
    wph
    @14
    wa
    #
    @2
    @11
    wcel
    @29
    wph
    cZ
    @11
    @1
    cF
    @13
    ffvelrnda
    @2
    cc
    cS
    elmapi
    syl
    #
    adantrr
    #
    ffvelrnda
    #
    @17
    cS
    cc
    @18
    cG
    @26
    ffvelrnda
    #
    nncand
    mpteq2dva
    eqtr4d
    @17
    vz
    cS
    @19
    @21
    cc
    @33
    @17
    @2
    vz
    cS
    @19
    cmpt
    cibl
    @17
    vz
    cS
    cc
    @2
    @32
    feqmptd
    #
    wph
    @14
    @2
    cibl
    wcel
    #
    @8
    wph
    cZ
    cibl
    @1
    cF
    itgulm.f
    ffvelrnda
    adantrr
    #
    eqeltrrd
    @28
    @19
    @20
    @33
    @34
    subcld
    #
    @17
    vz
    cS
    @21
    cmpt
    #
    cmbf
    wcel
    @39
    cdm
    #
    cvol
    cfv
    #
    cr
    wcel
    @0
    @39
    cfv
    #
    cabs
    cfv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vx
    @40
    wral
    #
    vr
    cr
    wrex
    #
    @39
    cibl
    wcel
    @17
    @2
    cG
    cmin
    cof
    co
    @39
    cmbf
    @17
    vz
    cS
    @19
    @20
    cmin
    @2
    cG
    cvv
    cc
    cc
    wph
    cS
    cvv
    wcel
    #
    @16
    wph
    @10
    @48
    itgulm.u
    cS
    cF
    cG
    ulmscl
    syl
    adantr
    @33
    @34
    @35
    @27
    offval2
    @17
    @2
    cG
    @17
    @36
    @2
    cmbf
    wcel
    @37
    @2
    iblmbf
    syl
    wph
    cG
    cmbf
    wcel
    @16
    wph
    cS
    cF
    cG
    cM
    cZ
    itgulm.z
    itgulm.m
    wph
    @12
    cibl
    cmbf
    wss
    cZ
    cmbf
    cF
    wf
    itgulm.f
    vx
    cibl
    cmbf
    @0
    iblmbf
    ssriv
    cZ
    cibl
    cmbf
    cF
    fss
    sylancl
    itgulm.u
    mbfulm
    adantr
    mbfsub
    eqeltrrd
    @17
    @41
    cS
    cvol
    cfv
    #
    cr
    @17
    @40
    cS
    cvol
    @17
    vz
    @39
    cS
    @21
    cc
    @39
    eqid
    #
    @38
    dmmptd
    #
    fveq2d
    wph
    @49
    cr
    wcel
    @16
    itgulm.s
    adantr
    eqeltrd
    @17
    c1
    cr
    wcel
    #
    @43
    c1
    cle
    wbr
    #
    vx
    @40
    wral
    #
    @47
    1re
    @17
    @54
    @53
    vx
    cS
    wral
    #
    wph
    @14
    @8
    @55
    @30
    @7
    @53
    vx
    cS
    @30
    @15
    wa
    #
    @7
    @6
    c1
    cle
    wbr
    #
    @53
    @56
    @6
    cr
    wcel
    @52
    @7
    @57
    wi
    @56
    @5
    @56
    @3
    @4
    @30
    cS
    cc
    @0
    @2
    @31
    ffvelrnda
    @30
    cS
    cc
    @0
    cG
    wph
    @24
    @14
    @25
    adantr
    ffvelrnda
    subcld
    abscld
    1re
    @6
    c1
    ltle
    sylancl
    @56
    @43
    @6
    c1
    cle
    @56
    @42
    @5
    cabs
    @15
    @42
    @5
    wceq
    @30
    vz
    @0
    @21
    @5
    cS
    @39
    @18
    @0
    wceq
    @19
    @3
    @20
    @4
    cmin
    @18
    @0
    @2
    fveq2
    @18
    @0
    cG
    fveq2
    oveq12d
    @50
    @3
    @4
    cmin
    ovex
    fvmpt
    adantl
    fveq2d
    breq1d
    sylibrd
    ralimdva
    impr
    @17
    @53
    vx
    @40
    cS
    @51
    raleqdv
    mpbird
    @46
    @54
    vr
    c1
    cr
    @44
    c1
    wceq
    @45
    @53
    vx
    @40
    @44
    c1
    @43
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    vr
    vx
    @39
    bddibl
    syl3anc
    iblsub
    eqeltrd
    rexlimddv
end
