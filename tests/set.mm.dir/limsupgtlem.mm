include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "clsp.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "cres.mm"
include "crn.mm"
include "cxr.mm"
include "csup.mm"
include "cmpt.mm"
include "cinf.mm"
include "cxad.mm"
include "nfv.mm"
include "uzn0d.mm"
include "wcel.mm"
include "wss.mm"
include "rnresss.mm"
include "a1i.mm"
include "frexr.mm"
include "frnd.mm"
include "sstrd.mm"
include "supxrcld.mm"
include "adantr.mm"
include "cr.mm"
include "wa.mm"
include "nfcv.mm"
include "limsupreuz.mm"
include "mpbid.mm"
include "simpld.mm"
include "rexr.mm"
include "ad4antlr.mm"
include "wf.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "3impa.mm"
include "ad5ant134.mm"
include "ad4antr.mm"
include "simpr.mm"
include "wceq.mm"
include "fvres.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wfn.mm"
include "ffnd.mm"
include "ssd.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "fnfvelrnd.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "supxrubd.mm"
include "xrletrd.mm"
include "rexlimdva2.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "rphalfcld.mm"
include "infrpgernmpt.mm"
include "w3a.mm"
include "simp3.mm"
include "limsupvaluz.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "breqtrd.mm"
include "caddc.mm"
include "3adantl3.mm"
include "simpl1.mm"
include "syl.mm"
include "cvv.mm"
include "fvexi.mm"
include "fexd.mm"
include "limsupcld.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "xaddcld.mm"
include "simpl3.mm"
include "rexaddd.mm"
include "wb.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "syld3an3.mm"
include "3exp.mm"
include "reximdai.mm"
include "wi.mm"
include "simpll.mm"
include "ffvelrnda.mm"
include "resubcld.mm"
include "rphalfltd.mm"
include "ltsub2dd.mm"
include "ltletrd.mm"
include "ex.mm"

theorem limsupgtlem
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume limsupgtlem.m: |- ( ph -> M e. ZZ )
  assume limsupgtlem.z: |- Z = ( ZZ>= ` M )
  assume limsupgtlem.f: |- ( ph -> F : Z --> RR )
  assume limsupgtlem.r: |- ( ph -> ( limsup ` F ) e. RR )
  assume limsupgtlem.x: |- ( ph -> X e. RR+ )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint F x
  disjoint j x
  disjoint k x
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) - X ) < ( limsup ` F ) )

  proof
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cX
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cF
    clsp
    cfv
    #
    cle
    wbr
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
    @1
    cX
    cmin
    co
    #
    @4
    clt
    wbr
    #
    vk
    @7
    wral
    #
    vj
    cZ
    wrex
    wph
    cF
    @7
    cres
    #
    crn
    #
    cxr
    clt
    csup
    #
    vj
    cZ
    @15
    cmpt
    crn
    cxr
    clt
    cinf
    #
    @2
    cxad
    co
    #
    cle
    wbr
    #
    vj
    cZ
    wrex
    @9
    wph
    vj
    vx
    cZ
    @15
    @2
    wph
    vj
    nfv
    #
    wph
    cM
    cZ
    limsupgtlem.m
    limsupgtlem.z
    uzn0d
    wph
    @15
    cxr
    wcel
    #
    @6
    cZ
    wcel
    #
    wph
    @14
    wph
    @14
    cF
    crn
    #
    cxr
    @14
    @22
    wss
    wph
    cF
    @7
    rnresss
    a1i
    wph
    cZ
    cxr
    cF
    wph
    cZ
    cF
    limsupgtlem.f
    frexr
    #
    frnd
    sstrd
    #
    supxrcld
    #
    adantr
    wph
    vx
    cv
    #
    @1
    cle
    wbr
    #
    vk
    @7
    wrex
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @26
    @15
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    wph
    @30
    @1
    @26
    cle
    wbr
    vk
    cZ
    wral
    vx
    cr
    wrex
    #
    wph
    @4
    cr
    wcel
    #
    @30
    @33
    wa
    limsupgtlem.r
    wph
    vx
    vk
    vj
    cF
    cM
    cZ
    vk
    cF
    nfcv
    limsupgtlem.m
    limsupgtlem.z
    limsupgtlem.f
    limsupreuz
    mpbid
    simpld
    wph
    @29
    @32
    vx
    cr
    wph
    @26
    cr
    wcel
    #
    wa
    #
    @28
    @31
    vj
    cZ
    @36
    @21
    wa
    #
    @27
    @31
    vk
    @7
    @37
    @0
    @7
    wcel
    #
    wa
    #
    @27
    wa
    @26
    @1
    @15
    @35
    @26
    cxr
    wcel
    wph
    @21
    @38
    @27
    @26
    rexr
    ad4antlr
    wph
    @21
    @38
    @1
    cxr
    wcel
    #
    @35
    @27
    wph
    @21
    @38
    @40
    wph
    @21
    wa
    #
    @38
    wa
    #
    @1
    @42
    cZ
    cr
    @0
    cF
    wph
    cZ
    cr
    cF
    wf
    @21
    @38
    limsupgtlem.f
    ad2antrr
    @21
    @38
    @0
    cZ
    wcel
    #
    wph
    cM
    @0
    @6
    cZ
    limsupgtlem.z
    uztrn2
    adantll
    #
    ffvelrnd
    #
    rexrd
    #
    3impa
    ad5ant134
    wph
    @20
    @35
    @21
    @38
    @27
    @25
    ad4antr
    @39
    @27
    simpr
    wph
    @21
    @38
    @1
    @15
    cle
    wbr
    #
    @35
    @27
    wph
    @21
    @38
    @47
    @42
    @14
    @1
    @15
    wph
    @14
    cxr
    wss
    @21
    @38
    @24
    ad2antrr
    @42
    @1
    @0
    @13
    cfv
    #
    @14
    @38
    @1
    @48
    wceq
    @41
    @38
    @48
    @1
    @0
    @7
    cF
    fvres
    eqcomd
    adantl
    @42
    @7
    @0
    @13
    @41
    @13
    @7
    wfn
    #
    @38
    @41
    cF
    cZ
    wfn
    #
    @7
    cZ
    wss
    @49
    wph
    @50
    @21
    wph
    cZ
    cr
    cF
    limsupgtlem.f
    ffnd
    adantr
    @41
    vk
    @7
    cZ
    @44
    ssd
    cZ
    @7
    cF
    fnssres
    syl2anc
    adantr
    @41
    @38
    simpr
    fnfvelrnd
    eqeltrd
    @15
    eqid
    supxrubd
    #
    3impa
    ad5ant134
    xrletrd
    rexlimdva2
    ralimdva
    reximdva
    mpd
    wph
    cX
    limsupgtlem.x
    rphalfcld
    infrpgernmpt
    wph
    @18
    @8
    vj
    cZ
    @19
    wph
    @21
    @18
    @8
    wph
    @21
    @18
    @15
    @4
    @2
    cxad
    co
    #
    cle
    wbr
    #
    @8
    wph
    @21
    @18
    w3a
    @15
    @17
    @52
    cle
    wph
    @21
    @18
    simp3
    wph
    @21
    @17
    @52
    wceq
    @18
    wph
    @16
    @4
    @2
    cxad
    wph
    @4
    @16
    wph
    vj
    cF
    cM
    cZ
    limsupgtlem.m
    limsupgtlem.z
    @23
    limsupvaluz
    eqcomd
    oveq1d
    3ad2ant1
    breqtrd
    wph
    @21
    @53
    w3a
    #
    @5
    vk
    @7
    @54
    @38
    wa
    #
    @5
    @1
    @4
    @2
    caddc
    co
    #
    cle
    wbr
    #
    @55
    @1
    @52
    @56
    cle
    @55
    @1
    @15
    @52
    wph
    @21
    @38
    @40
    @53
    @46
    3adantl3
    @55
    wph
    @20
    wph
    @21
    @53
    @38
    simpl1
    #
    @25
    syl
    @55
    wph
    @52
    cxr
    wcel
    @58
    wph
    @4
    @2
    wph
    cF
    cvv
    wph
    cZ
    cr
    cvv
    cF
    limsupgtlem.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    limsupgtlem.z
    fvexi
    a1i
    fexd
    limsupcld
    wph
    @2
    wph
    cX
    wph
    cX
    limsupgtlem.x
    rpred
    #
    rehalfcld
    #
    rexrd
    xaddcld
    syl
    wph
    @21
    @38
    @47
    @53
    @51
    3adantl3
    wph
    @21
    @53
    @38
    simpl3
    xrletrd
    @55
    wph
    @52
    @56
    wceq
    @58
    wph
    @4
    @2
    limsupgtlem.r
    @60
    rexaddd
    syl
    breqtrd
    wph
    @21
    @38
    @5
    @57
    wb
    @53
    @42
    @1
    @2
    @4
    @45
    wph
    @2
    cr
    wcel
    #
    @21
    @38
    @60
    ad2antrr
    wph
    @34
    @21
    @38
    limsupgtlem.r
    ad2antrr
    lesubaddd
    3adantl3
    mpbird
    ralrimiva
    syld3an3
    3exp
    reximdai
    mpd
    wph
    @8
    @12
    vj
    cZ
    @41
    @5
    @11
    vk
    @7
    @42
    wph
    @43
    @5
    @11
    wi
    wph
    @21
    @38
    simpll
    @44
    wph
    @43
    wa
    #
    @5
    @11
    @62
    @5
    wa
    @10
    @3
    @4
    @62
    @10
    cr
    wcel
    @5
    @62
    @1
    cX
    wph
    cZ
    cr
    @0
    cF
    limsupgtlem.f
    ffvelrnda
    #
    wph
    cX
    cr
    wcel
    @43
    @59
    adantr
    #
    resubcld
    adantr
    @62
    @3
    cr
    wcel
    @5
    @62
    @1
    @2
    @63
    wph
    @61
    @43
    @60
    adantr
    #
    resubcld
    adantr
    wph
    @34
    @43
    @5
    limsupgtlem.r
    ad2antrr
    @62
    @10
    @3
    clt
    wbr
    @5
    @62
    @2
    cX
    @1
    @65
    @64
    @63
    wph
    @2
    cX
    clt
    wbr
    @43
    wph
    cX
    limsupgtlem.x
    rphalfltd
    adantr
    ltsub2dd
    adantr
    @62
    @5
    simpr
    ltletrd
    ex
    syl2anc
    ralimdva
    reximdva
    mpd
end
