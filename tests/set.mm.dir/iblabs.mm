include "cabs.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "cif.mm"
include "citg2.mm"
include "ccom.mm"
include "cc.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "eqidd.mm"
include "wf.mm"
include "absf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "ccncf.mm"
include "co.mm"
include "eqid.mm"
include "fmptd.mm"
include "wss.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "abscncf.mm"
include "sselii.mm"
include "cncombf.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "cpnf.mm"
include "cicc.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "abscld.mm"
include "rexrd.mm"
include "absge0d.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "ifclda.mm"
include "adantr.mm"
include "cof.mm"
include "cvv.mm"
include "cico.mm"
include "reex.mm"
include "recld.mm"
include "recnd.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "imcld.mm"
include "offval2.mm"
include "wceq.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "00id.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "syl6req.mm"
include "fveq2d.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "iblabslem.mm"
include "simprd.mm"
include "itg2add.mm"
include "eqtrd.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "cofr.mm"
include "addge0d.mm"
include "wral.mm"
include "ci.mm"
include "cmul.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "abstrid.mm"
include "replimd.mm"
include "absmul.mm"
include "c1.mm"
include "absi.mm"
include "oveq1i.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "3brtr4d.mm"
include "adantl.mm"
include "ex.mm"
include "0le0.mm"
include "pm2.61d1.mm"
include "ralrimivw.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "itg2lecl.mm"
include "iblpos.mm"
include "mpbir2and.mm"

theorem iblabs
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  let cF: class F
  assume iblabs.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume iblabs.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( ph -> ( x e. A |-> ( abs ` B ) ) e. L^1 )

  proof
    wph
    vx
    cA
    cB
    cabs
    cfv
    #
    cmpt
    #
    cibl
    wcel
    @1
    cmbf
    wcel
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    wph
    cabs
    vx
    cA
    cB
    cmpt
    #
    ccom
    #
    @1
    cmbf
    wph
    vx
    vy
    cA
    cc
    cB
    vy
    cv
    #
    cabs
    cfv
    @0
    @8
    cabs
    wph
    vx
    cA
    cB
    cV
    wph
    @8
    cibl
    wcel
    #
    @8
    cmbf
    wcel
    #
    iblabs.2
    @8
    iblmbf
    syl
    #
    iblabs.1
    mbfmptcl
    #
    wph
    @8
    eqidd
    wph
    vy
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    wph
    absf
    a1i
    feqmptd
    @10
    cB
    cabs
    fveq2
    fmptco
    wph
    @12
    cA
    cc
    @8
    wf
    cabs
    cc
    cc
    ccncf
    co
    #
    wcel
    #
    @9
    cmbf
    wcel
    @13
    wph
    vx
    cA
    cB
    cc
    @8
    @14
    @8
    eqid
    fmptd
    @16
    wph
    cc
    cr
    ccncf
    co
    #
    @15
    cabs
    cr
    cc
    wss
    cc
    cc
    wss
    @17
    @15
    wss
    ax-resscn
    cc
    ssid
    cc
    cr
    cc
    cncfss
    mp2an
    abscncf
    sselii
    a1i
    cA
    cc
    @8
    cabs
    cncombf
    syl3anc
    eqeltrrd
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    @5
    wf
    #
    vx
    cr
    @3
    cB
    cre
    cfv
    #
    cabs
    cfv
    #
    cB
    cim
    cfv
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    @6
    @27
    cle
    wbr
    #
    @7
    wph
    vx
    cr
    @4
    @18
    @5
    wph
    @4
    @18
    wcel
    @2
    cr
    wcel
    #
    wph
    @3
    @0
    cc0
    @18
    wph
    @3
    wa
    #
    @0
    cxr
    wcel
    cc0
    @0
    cle
    wbr
    @0
    @18
    wcel
    @30
    @0
    @30
    cB
    @14
    abscld
    #
    rexrd
    @30
    cB
    @14
    absge0d
    #
    @0
    elxrge0
    sylanbrc
    cc0
    @18
    wcel
    wph
    @3
    wn
    #
    wa
    #
    0e0iccpnf
    a1i
    #
    ifclda
    adantr
    #
    @5
    eqid
    fmptd
    #
    wph
    @27
    vx
    cr
    @3
    @21
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cr
    @3
    @23
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    #
    cr
    wph
    @27
    @39
    @42
    caddc
    cof
    co
    #
    citg2
    cfv
    @44
    wph
    @26
    @45
    citg2
    wph
    @45
    vx
    cr
    @38
    @41
    caddc
    co
    #
    cmpt
    @26
    wph
    vx
    cr
    @38
    @41
    caddc
    @39
    @42
    cvv
    cc0
    cpnf
    cico
    co
    #
    @47
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    wph
    @38
    @47
    wcel
    @29
    wph
    @3
    @21
    cc0
    @47
    @30
    @21
    cr
    wcel
    cc0
    @21
    cle
    wbr
    @21
    @47
    wcel
    @30
    @20
    @30
    @20
    @30
    cB
    @14
    recld
    #
    recnd
    #
    abscld
    #
    @30
    @20
    @50
    absge0d
    #
    @21
    elrege0
    sylanbrc
    cc0
    @47
    wcel
    @34
    0e0icopnf
    a1i
    #
    ifclda
    adantr
    #
    wph
    @41
    @47
    wcel
    @29
    wph
    @3
    @23
    cc0
    @47
    @30
    @23
    cr
    wcel
    cc0
    @23
    cle
    wbr
    @23
    @47
    wcel
    @30
    @22
    @30
    @22
    @30
    cB
    @14
    imcld
    #
    recnd
    #
    abscld
    #
    @30
    @22
    @56
    absge0d
    #
    @23
    elrege0
    sylanbrc
    @53
    ifclda
    adantr
    #
    wph
    @39
    eqidd
    wph
    @42
    eqidd
    offval2
    vx
    cr
    @46
    @25
    @3
    @46
    @25
    wceq
    @3
    @46
    @24
    @25
    @3
    @38
    @21
    @41
    @23
    caddc
    @3
    @21
    cc0
    iftrue
    @3
    @23
    cc0
    iftrue
    oveq12d
    @3
    @24
    cc0
    iftrue
    #
    eqtr4d
    @33
    cc0
    cc0
    caddc
    co
    cc0
    @46
    @25
    00id
    @33
    @38
    cc0
    @41
    cc0
    caddc
    @3
    @21
    cc0
    iffalse
    @3
    @23
    cc0
    iffalse
    oveq12d
    @3
    @24
    cc0
    iffalse
    #
    3eqtr4a
    pm2.61i
    mpteq2i
    syl6req
    fveq2d
    wph
    @39
    @42
    wph
    @39
    cmbf
    wcel
    #
    @40
    cr
    wcel
    #
    wph
    vx
    cA
    cB
    cre
    @39
    cV
    iblabs.1
    iblabs.2
    @39
    eqid
    #
    wph
    vx
    cA
    @20
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @22
    cmpt
    cibl
    wcel
    #
    wph
    @11
    @65
    @66
    wa
    iblabs.2
    wph
    vx
    cA
    cB
    @14
    iblcn
    mpbid
    #
    simpld
    @49
    iblabslem
    #
    simpld
    wph
    vx
    cr
    @38
    @47
    @39
    @54
    @64
    fmptd
    wph
    @62
    @63
    @68
    simprd
    #
    wph
    @42
    cmbf
    wcel
    #
    @43
    cr
    wcel
    #
    wph
    vx
    cA
    cB
    cim
    @42
    cV
    iblabs.1
    iblabs.2
    @42
    eqid
    #
    wph
    @65
    @66
    @67
    simprd
    @55
    iblabslem
    #
    simpld
    wph
    vx
    cr
    @41
    @47
    @42
    @59
    @72
    fmptd
    wph
    @70
    @71
    @73
    simprd
    #
    itg2add
    eqtrd
    wph
    @40
    @43
    @69
    @74
    readdcld
    eqeltrd
    wph
    @19
    cr
    @18
    @26
    wf
    @5
    @26
    cle
    cofr
    wbr
    #
    @28
    @37
    wph
    vx
    cr
    @25
    @18
    @26
    wph
    @25
    @18
    wcel
    @29
    wph
    @3
    @24
    cc0
    @18
    @30
    @24
    cxr
    wcel
    cc0
    @24
    cle
    wbr
    @24
    @18
    wcel
    @30
    @24
    @30
    @21
    @23
    @51
    @57
    readdcld
    rexrd
    @30
    @21
    @23
    @51
    @57
    @52
    @58
    addge0d
    @24
    elxrge0
    sylanbrc
    @35
    ifclda
    adantr
    #
    @26
    eqid
    fmptd
    wph
    @75
    @4
    @25
    cle
    wbr
    #
    vx
    cr
    wral
    wph
    @77
    vx
    cr
    wph
    @3
    @77
    wph
    @3
    @77
    @30
    @0
    @24
    @4
    @25
    cle
    @30
    @20
    ci
    @22
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    @21
    @78
    cabs
    cfv
    #
    caddc
    co
    @0
    @24
    cle
    @30
    @20
    @78
    @50
    @30
    ci
    cc
    wcel
    #
    @22
    cc
    wcel
    #
    @78
    cc
    wcel
    ax-icn
    @56
    ci
    @22
    mulcl
    sylancr
    abstrid
    @30
    cB
    @79
    cabs
    @30
    cB
    @14
    replimd
    fveq2d
    @30
    @23
    @80
    @21
    caddc
    @30
    @80
    ci
    cabs
    cfv
    #
    @23
    cmul
    co
    #
    @23
    @30
    @81
    @82
    @80
    @84
    wceq
    ax-icn
    @56
    ci
    @22
    absmul
    sylancr
    @30
    @84
    c1
    @23
    cmul
    co
    @23
    @83
    c1
    @23
    cmul
    absi
    oveq1i
    @30
    @23
    @30
    @23
    @57
    recnd
    mulid2d
    syl5eq
    eqtr2d
    oveq2d
    3brtr4d
    @3
    @4
    @0
    wceq
    wph
    @3
    @0
    cc0
    iftrue
    adantl
    @3
    @25
    @24
    wceq
    wph
    @60
    adantl
    3brtr4d
    ex
    @33
    cc0
    cc0
    @4
    @25
    cle
    cc0
    cc0
    cle
    wbr
    @33
    0le0
    a1i
    @3
    @0
    cc0
    iffalse
    @61
    3brtr4d
    pm2.61d1
    ralrimivw
    wph
    vx
    cr
    @4
    @25
    cle
    @5
    @26
    cvv
    @18
    @18
    @48
    @36
    @76
    wph
    @5
    eqidd
    wph
    @26
    eqidd
    ofrfval2
    mpbird
    @5
    @26
    itg2le
    syl3anc
    @27
    @5
    itg2lecl
    syl3anc
    wph
    vx
    cA
    @0
    @31
    @32
    iblpos
    mpbir2and
end
