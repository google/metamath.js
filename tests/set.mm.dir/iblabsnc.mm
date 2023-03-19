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
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "abscld.mm"
include "rexrd.mm"
include "absge0d.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cof.mm"
include "cvv.mm"
include "cico.mm"
include "reex.mm"
include "recld.mm"
include "recnd.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "imcld.mm"
include "eqidd.mm"
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
include "iblabsnclem.mm"
include "simprd.mm"
include "itg2addnc.mm"
include "eqtrd.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "cofr.mm"
include "addge0d.mm"
include "wral.mm"
include "ci.mm"
include "cmul.mm"
include "cc.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "abstrid.mm"
include "adantl.mm"
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
include "ex.mm"
include "0le0.mm"
include "pm2.61d1.mm"
include "ralrimivw.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"
include "iblpos.mm"
include "mpbir2and.mm"

theorem iblabsnc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  assume iblabsnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume iblabsnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume iblabsnc.m: |- ( ph -> ( x e. A |-> ( abs ` B ) ) e. MblFn )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint B y
  disjoint V y
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
    iblabsnc.m
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
    @17
    cle
    wbr
    #
    @7
    wph
    vx
    cr
    @4
    @8
    @5
    wph
    @4
    @8
    wcel
    @2
    cr
    wcel
    #
    wph
    @3
    @0
    cc0
    @8
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
    @8
    wcel
    @20
    @0
    @20
    cB
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
    @21
    cmbf
    wcel
    iblabsnc.2
    @21
    iblmbf
    syl
    iblabsnc.1
    mbfmptcl
    #
    abscld
    #
    rexrd
    @20
    cB
    @23
    absge0d
    #
    @0
    elxrge0
    sylanbrc
    cc0
    @8
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
    @17
    vx
    cr
    @3
    @11
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
    @13
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
    @17
    @32
    @35
    caddc
    cof
    co
    #
    citg2
    cfv
    @37
    wph
    @16
    @38
    citg2
    wph
    @38
    vx
    cr
    @31
    @34
    caddc
    co
    #
    cmpt
    @16
    wph
    vx
    cr
    @31
    @34
    caddc
    @32
    @35
    cvv
    cc0
    cpnf
    cico
    co
    #
    @40
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    wph
    @31
    @40
    wcel
    @19
    wph
    @3
    @11
    cc0
    @40
    @20
    @11
    cr
    wcel
    cc0
    @11
    cle
    wbr
    @11
    @40
    wcel
    @20
    @10
    @20
    @10
    @20
    cB
    @23
    recld
    #
    recnd
    #
    abscld
    #
    @20
    @10
    @43
    absge0d
    #
    @11
    elrege0
    sylanbrc
    cc0
    @40
    wcel
    @27
    0e0icopnf
    a1i
    #
    ifclda
    adantr
    #
    wph
    @34
    @40
    wcel
    @19
    wph
    @3
    @13
    cc0
    @40
    @20
    @13
    cr
    wcel
    cc0
    @13
    cle
    wbr
    @13
    @40
    wcel
    @20
    @12
    @20
    @12
    @20
    cB
    @23
    imcld
    #
    recnd
    #
    abscld
    #
    @20
    @12
    @49
    absge0d
    #
    @13
    elrege0
    sylanbrc
    @46
    ifclda
    adantr
    #
    wph
    @32
    eqidd
    wph
    @35
    eqidd
    offval2
    vx
    cr
    @39
    @15
    @3
    @39
    @15
    wceq
    @3
    @39
    @14
    @15
    @3
    @31
    @11
    @34
    @13
    caddc
    @3
    @11
    cc0
    iftrue
    @3
    @13
    cc0
    iftrue
    oveq12d
    @3
    @14
    cc0
    iftrue
    #
    eqtr4d
    @26
    cc0
    cc0
    caddc
    co
    cc0
    @39
    @15
    00id
    @26
    @31
    cc0
    @34
    cc0
    caddc
    @3
    @11
    cc0
    iffalse
    @3
    @13
    cc0
    iffalse
    oveq12d
    @3
    @14
    cc0
    iffalse
    #
    3eqtr4a
    pm2.61i
    mpteq2i
    syl6req
    fveq2d
    wph
    @32
    @35
    wph
    @32
    cmbf
    wcel
    #
    @33
    cr
    wcel
    #
    wph
    vx
    cA
    cB
    cre
    @32
    cV
    iblabsnc.1
    iblabsnc.2
    @32
    eqid
    #
    wph
    vx
    cA
    @10
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @12
    cmpt
    cibl
    wcel
    #
    wph
    @22
    @58
    @59
    wa
    iblabsnc.2
    wph
    vx
    cA
    cB
    @23
    iblcn
    mpbid
    #
    simpld
    @42
    iblabsnclem
    #
    simpld
    wph
    vx
    cr
    @31
    @40
    @32
    @47
    @57
    fmptd
    wph
    @55
    @56
    @61
    simprd
    #
    wph
    vx
    cr
    @34
    @40
    @35
    @52
    @35
    eqid
    #
    fmptd
    wph
    @35
    cmbf
    wcel
    @36
    cr
    wcel
    wph
    vx
    cA
    cB
    cim
    @35
    cV
    iblabsnc.1
    iblabsnc.2
    @63
    wph
    @58
    @59
    @60
    simprd
    @48
    iblabsnclem
    simprd
    #
    itg2addnc
    eqtrd
    wph
    @33
    @36
    @62
    @64
    readdcld
    eqeltrd
    wph
    @9
    cr
    @8
    @16
    wf
    @5
    @16
    cle
    cofr
    wbr
    #
    @18
    @30
    wph
    vx
    cr
    @15
    @8
    @16
    wph
    @15
    @8
    wcel
    @19
    wph
    @3
    @14
    cc0
    @8
    @20
    @14
    cxr
    wcel
    cc0
    @14
    cle
    wbr
    @14
    @8
    wcel
    @20
    @14
    @20
    @11
    @13
    @44
    @50
    readdcld
    rexrd
    @20
    @11
    @13
    @44
    @50
    @45
    @51
    addge0d
    @14
    elxrge0
    sylanbrc
    @28
    ifclda
    adantr
    #
    @16
    eqid
    fmptd
    wph
    @65
    @4
    @15
    cle
    wbr
    #
    vx
    cr
    wral
    wph
    @67
    vx
    cr
    wph
    @3
    @67
    wph
    @3
    @67
    @20
    @10
    ci
    @12
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    @11
    @68
    cabs
    cfv
    #
    caddc
    co
    #
    @4
    @15
    cle
    @20
    @10
    @68
    @43
    @20
    ci
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @68
    cc
    wcel
    ax-icn
    @49
    ci
    @12
    mulcl
    sylancr
    abstrid
    @20
    @4
    @0
    @70
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
    @20
    cB
    @69
    cabs
    @20
    cB
    @23
    replimd
    fveq2d
    eqtrd
    @20
    @15
    @14
    @72
    @3
    @15
    @14
    wceq
    wph
    @53
    adantl
    @20
    @13
    @71
    @11
    caddc
    @20
    @71
    ci
    cabs
    cfv
    #
    @13
    cmul
    co
    #
    @13
    @20
    @73
    @74
    @71
    @76
    wceq
    ax-icn
    @49
    ci
    @12
    absmul
    sylancr
    @20
    @76
    c1
    @13
    cmul
    co
    @13
    @75
    c1
    @13
    cmul
    absi
    oveq1i
    @20
    @13
    @20
    @13
    @50
    recnd
    mulid2d
    syl5eq
    eqtr2d
    oveq2d
    eqtrd
    3brtr4d
    ex
    @26
    cc0
    cc0
    @4
    @15
    cle
    cc0
    cc0
    cle
    wbr
    @26
    0le0
    a1i
    @3
    @0
    cc0
    iffalse
    @54
    3brtr4d
    pm2.61d1
    ralrimivw
    wph
    vx
    cr
    @4
    @15
    cle
    @5
    @16
    cvv
    @8
    @8
    @41
    @29
    @66
    wph
    @5
    eqidd
    wph
    @16
    eqidd
    ofrfval2
    mpbird
    @5
    @16
    itg2le
    syl3anc
    @17
    @5
    itg2lecl
    syl3anc
    wph
    vx
    cA
    @0
    @24
    @25
    iblpos
    mpbir2and
end
