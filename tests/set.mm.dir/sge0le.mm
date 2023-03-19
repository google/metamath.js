include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "sge0xrcl.mm"
include "pnfge.mm"
include "syl.mm"
include "adantr.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "cv.mm"
include "cres.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "csu.mm"
include "cr.mm"
include "elinel2.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cicc.mm"
include "crn.mm"
include "wrex.mm"
include "simpr.mm"
include "wb.mm"
include "wfn.mm"
include "ffnd.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "iccssxr.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "eqbrtrd.mm"
include "xrgepnfd.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "adantlr.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "sge0pnfval.mm"
include "simplr.mm"
include "pm2.65da.mm"
include "fge0iccico.mm"
include "wss.mm"
include "elpwinss.mm"
include "fssresd.mm"
include "sge0fsum.mm"
include "rge0ssre.mm"
include "fsumrecl.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "sge0rern.mm"
include "simplll.mm"
include "sselda.mm"
include "fvres.mm"
include "breq12d.mm"
include "fsumle.mm"
include "sge0less.mm"
include "letrd.mm"
include "ralrimiva.mm"
include "sge0lefi.mm"
include "pm2.61dan.mm"

theorem sge0le
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume sge0le.x: |- ( ph -> X e. V )
  assume sge0le.F: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0le.g: |- ( ph -> G : X --> ( 0 [,] +oo ) )
  assume sge0le.le: |- ( ( ph /\ x e. X ) -> ( F ` x ) <_ ( G ` x ) )

  disjoint F x
  disjoint G x
  disjoint X x
  disjoint ph x
  disjoint F y
  disjoint x y
  disjoint G y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) <_ ( sum^ ` G ) )

  proof
    wph
    cG
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    cF
    csumge0
    cfv
    #
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    @2
    cpnf
    @0
    cle
    wph
    @2
    cpnf
    cle
    wbr
    #
    @1
    wph
    @2
    cxr
    wcel
    @4
    wph
    cF
    cV
    cX
    sge0le.x
    sge0le.F
    sge0xrcl
    @2
    pnfge
    syl
    adantr
    @1
    cpnf
    @0
    wceq
    wph
    @1
    @0
    cpnf
    @1
    id
    eqcomd
    adantl
    breqtrd
    wph
    @1
    wn
    #
    wa
    #
    @3
    cF
    vy
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    @0
    cle
    wbr
    #
    vy
    cX
    cpw
    #
    cfn
    cin
    #
    wral
    @6
    @10
    vy
    @12
    @6
    @7
    @12
    wcel
    #
    wa
    #
    @9
    cG
    @7
    cres
    #
    csumge0
    cfv
    #
    @0
    @14
    @9
    @7
    vx
    cv
    #
    @8
    cfv
    #
    vx
    csu
    #
    cr
    @14
    vx
    @8
    @7
    @13
    @7
    cfn
    wcel
    @6
    @7
    @11
    cfn
    elinel2
    adantl
    #
    @14
    cX
    cc0
    cpnf
    cico
    co
    #
    @7
    cF
    @6
    cX
    @21
    cF
    wf
    @13
    @6
    cF
    cX
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    @5
    sge0le.F
    adantr
    #
    @6
    cpnf
    cF
    crn
    wcel
    #
    @1
    wph
    @24
    @1
    @5
    wph
    @24
    wa
    #
    cG
    cV
    cX
    wph
    cX
    cV
    wcel
    #
    @24
    sge0le.x
    adantr
    wph
    cX
    @22
    cG
    wf
    #
    @24
    sge0le.g
    adantr
    @25
    @17
    cF
    cfv
    #
    cpnf
    wceq
    #
    vx
    cX
    wrex
    #
    cpnf
    cG
    crn
    #
    wcel
    #
    @25
    @24
    @30
    wph
    @24
    simpr
    wph
    @24
    @30
    wb
    #
    @24
    wph
    cF
    cX
    wfn
    @33
    wph
    cX
    @22
    cF
    sge0le.F
    ffnd
    vx
    cX
    cpnf
    cF
    fvelrnb
    syl
    adantr
    mpbid
    @25
    @29
    @32
    vx
    cX
    wph
    @17
    cX
    wcel
    #
    @29
    @32
    wi
    @24
    wph
    @34
    wa
    #
    @29
    @32
    @35
    @29
    wa
    #
    cpnf
    @17
    cG
    cfv
    #
    @31
    @36
    @37
    cpnf
    @36
    @37
    @35
    @37
    cxr
    wcel
    @29
    @35
    @22
    cxr
    @37
    cc0
    cpnf
    iccssxr
    wph
    cX
    @22
    @17
    cG
    sge0le.g
    ffvelrnda
    sseldi
    adantr
    @36
    cpnf
    @28
    @37
    cle
    @29
    cpnf
    @28
    wceq
    @35
    @29
    @28
    cpnf
    @29
    id
    eqcomd
    adantl
    @35
    @28
    @37
    cle
    wbr
    #
    @29
    sge0le.le
    adantr
    eqbrtrd
    xrgepnfd
    eqcomd
    @35
    @37
    @31
    wcel
    #
    @29
    @35
    cG
    cX
    wfn
    #
    @34
    @39
    wph
    @40
    @34
    wph
    cX
    @22
    cG
    sge0le.g
    ffnd
    adantr
    wph
    @34
    simpr
    cX
    @17
    cG
    fnfvelrn
    syl2anc
    adantr
    eqeltrd
    ex
    adantlr
    rexlimdva
    mpd
    sge0pnfval
    adantlr
    wph
    @5
    @24
    simplr
    pm2.65da
    fge0iccico
    adantr
    @13
    @7
    cX
    wss
    @6
    @7
    cX
    cfn
    elpwinss
    adantl
    #
    fssresd
    #
    sge0fsum
    #
    @14
    @7
    @18
    vx
    @20
    @14
    @17
    @7
    wcel
    #
    wa
    #
    @21
    cr
    @18
    rge0ssre
    @14
    @7
    @21
    @17
    @8
    @42
    ffvelrnda
    sseldi
    #
    fsumrecl
    eqeltrd
    @14
    @16
    @7
    @17
    @15
    cfv
    #
    vx
    csu
    #
    cr
    @14
    vx
    @15
    @7
    @20
    @14
    cX
    @21
    @7
    cG
    @6
    cX
    @21
    cG
    wf
    @13
    @6
    cG
    cX
    wph
    @27
    @5
    sge0le.g
    adantr
    #
    @6
    cG
    cV
    cX
    wph
    @26
    @5
    sge0le.x
    adantr
    #
    @49
    @6
    @0
    cr
    wcel
    #
    @5
    wph
    @5
    simpr
    @6
    cG
    cV
    cX
    @50
    @49
    sge0repnf
    mpbird
    #
    sge0rern
    fge0iccico
    adantr
    @41
    fssresd
    #
    sge0fsum
    #
    @14
    @7
    @47
    vx
    @20
    @45
    @21
    cr
    @47
    rge0ssre
    @14
    @7
    @21
    @17
    @15
    @53
    ffvelrnda
    sseldi
    #
    fsumrecl
    eqeltrd
    @6
    @51
    @13
    @52
    adantr
    @14
    @9
    @16
    cle
    wbr
    @19
    @48
    cle
    wbr
    @14
    @7
    @18
    @47
    vx
    @20
    @46
    @55
    @45
    @18
    @47
    cle
    wbr
    @38
    @45
    wph
    @34
    @38
    wph
    @5
    @13
    @44
    simplll
    @14
    @7
    cX
    @17
    @41
    sselda
    sge0le.le
    syl2anc
    @45
    @18
    @28
    @47
    @37
    cle
    @44
    @18
    @28
    wceq
    @14
    @17
    @7
    cF
    fvres
    adantl
    @44
    @47
    @37
    wceq
    @14
    @17
    @7
    cG
    fvres
    adantl
    breq12d
    mpbird
    fsumle
    @14
    @9
    @19
    @16
    @48
    cle
    @43
    @54
    breq12d
    mpbird
    wph
    @13
    @16
    @0
    cle
    wbr
    @5
    wph
    @13
    wa
    cG
    cV
    cX
    @7
    wph
    @26
    @13
    sge0le.x
    adantr
    wph
    @27
    @13
    sge0le.g
    adantr
    sge0less
    adantlr
    letrd
    ralrimiva
    @6
    vy
    @0
    cF
    cV
    cX
    @50
    @23
    @6
    cG
    cV
    cX
    @50
    @49
    sge0xrcl
    sge0lefi
    mpbird
    pm2.61dan
end
