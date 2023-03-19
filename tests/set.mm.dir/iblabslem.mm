include "cmbf.mm"
include "wcel.mm"
include "citg2.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cibl.mm"
include "w3a.mm"
include "iblrelem.mm"
include "mpbid.mm"
include "simp1d.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "syl.mm"
include "rembl.mm"
include "a1i.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "recnd.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "iffalse.mm"
include "ccom.mm"
include "cc.mm"
include "eqidd.mm"
include "wf.mm"
include "absf.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "mpteq2ia.mm"
include "syl6reqr.mm"
include "ccncf.mm"
include "co.mm"
include "eqid.mm"
include "fmptd.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "abscncf.mm"
include "sselii.mm"
include "cncombf.mm"
include "syl3anc.mm"
include "mbfss.mm"
include "syl5eqel.mm"
include "caddc.mm"
include "cof.mm"
include "cvv.mm"
include "cpnf.mm"
include "cico.mm"
include "reex.mm"
include "ifan.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "0e0icopnf.mm"
include "ifclda.mm"
include "adantr.mm"
include "renegcld.mm"
include "offval2.mm"
include "oveq12i.mm"
include "max0add.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "00id.mm"
include "3eqtr4a.mm"
include "pm2.61d1.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ibar.mm"
include "ifbid.mm"
include "mbfpos.mm"
include "syl5eqelr.mm"
include "simp2d.mm"
include "mbfneg.mm"
include "simp3d.mm"
include "itg2add.mm"
include "readdcld.mm"
include "jca.mm"

theorem iblabslem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vy: setvar y
  assume iblabs.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume iblabs.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume iblabs.3: |- G = ( x e. RR |-> if ( x e. A , ( abs ` ( F ` B ) ) , 0 ) )
  assume iblabs.4: |- ( ph -> ( x e. A |-> ( F ` B ) ) e. L^1 )
  assume iblabs.5: |- ( ( ph /\ x e. A ) -> ( F ` B ) e. RR )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( ph -> ( G e. MblFn /\ ( S.2 ` G ) e. RR ) )

  proof
    wph
    cG
    cmbf
    wcel
    cG
    citg2
    cfv
    #
    cr
    wcel
    wph
    cG
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cF
    cfv
    #
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cmbf
    iblabs.3
    wph
    vx
    cA
    cr
    @5
    cr
    wph
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    wss
    wph
    vx
    cA
    @3
    cr
    wph
    vx
    cA
    @3
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cr
    @2
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @3
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
    vx
    cr
    @2
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    wa
    #
    @16
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
    @8
    cibl
    wcel
    @9
    @15
    @22
    w3a
    iblabs.4
    wph
    vx
    cA
    @3
    iblabs.5
    iblrelem
    mpbid
    #
    simp1d
    #
    iblabs.5
    mbfdm2
    cA
    mblss
    syl
    #
    cr
    @7
    wcel
    wph
    rembl
    a1i
    #
    wph
    @2
    wa
    #
    @5
    @4
    cr
    @2
    @5
    @4
    wceq
    wph
    @2
    @4
    cc0
    iftrue
    #
    adantl
    #
    @27
    @3
    @27
    @3
    iblabs.5
    recnd
    #
    abscld
    eqeltrd
    wph
    @1
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    @2
    wn
    #
    @5
    cc0
    wceq
    @31
    @33
    wph
    @1
    cr
    cA
    eldifn
    adantl
    #
    @2
    @4
    cc0
    iffalse
    #
    syl
    wph
    vx
    cA
    @5
    cmpt
    #
    cabs
    @8
    ccom
    #
    cmbf
    wph
    @37
    vx
    cA
    @4
    cmpt
    @36
    wph
    vx
    vy
    cA
    cc
    @3
    vy
    cv
    #
    cabs
    cfv
    @4
    @8
    cabs
    @30
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
    @38
    @3
    cabs
    fveq2
    fmptco
    vx
    cA
    @5
    @4
    @28
    mpteq2ia
    syl6reqr
    wph
    @9
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
    @37
    cmbf
    wcel
    @24
    wph
    vx
    cA
    @3
    cc
    @8
    @30
    @8
    eqid
    fmptd
    @40
    wph
    cc
    cr
    ccncf
    co
    #
    @39
    cabs
    cr
    cc
    wss
    cc
    cc
    wss
    @41
    @39
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
    eqeltrd
    mbfss
    syl5eqel
    wph
    @0
    @14
    @21
    caddc
    co
    #
    cr
    wph
    @0
    @13
    @20
    caddc
    cof
    co
    #
    citg2
    cfv
    @42
    wph
    cG
    @43
    citg2
    wph
    @43
    @6
    cG
    wph
    @43
    vx
    cr
    @12
    @19
    caddc
    co
    #
    cmpt
    @6
    wph
    vx
    cr
    @12
    @19
    caddc
    @13
    @20
    cvv
    cc0
    cpnf
    cico
    co
    #
    @45
    cr
    cvv
    wcel
    wph
    reex
    a1i
    wph
    @12
    @45
    wcel
    #
    @1
    cr
    wcel
    #
    wph
    @12
    @2
    @10
    @3
    cc0
    cif
    #
    cc0
    cif
    #
    @45
    @2
    @10
    @3
    cc0
    ifan
    #
    wph
    @2
    @48
    cc0
    @45
    @27
    @48
    cr
    wcel
    #
    cc0
    @48
    cle
    wbr
    #
    @48
    @45
    wcel
    @27
    @3
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @51
    iblabs.5
    0re
    @10
    @3
    cc0
    cr
    ifcl
    sylancl
    @27
    @54
    @53
    @52
    0re
    iblabs.5
    cc0
    @3
    max1
    sylancr
    @48
    elrege0
    sylanbrc
    cc0
    @45
    wcel
    wph
    @33
    wa
    0e0icopnf
    a1i
    #
    ifclda
    syl5eqel
    #
    adantr
    #
    wph
    @19
    @45
    wcel
    #
    @47
    wph
    @19
    @2
    @17
    @16
    cc0
    cif
    #
    cc0
    cif
    #
    @45
    @2
    @17
    @16
    cc0
    ifan
    #
    wph
    @2
    @59
    cc0
    @45
    @27
    @59
    cr
    wcel
    #
    cc0
    @59
    cle
    wbr
    #
    @59
    @45
    wcel
    @27
    @16
    cr
    wcel
    #
    @54
    @62
    @27
    @3
    iblabs.5
    renegcld
    #
    0re
    @17
    @16
    cc0
    cr
    ifcl
    sylancl
    @27
    @54
    @64
    @63
    0re
    @65
    cc0
    @16
    max1
    sylancr
    @59
    elrege0
    sylanbrc
    @55
    ifclda
    syl5eqel
    #
    adantr
    #
    wph
    @13
    eqidd
    wph
    @20
    eqidd
    offval2
    wph
    vx
    cr
    @44
    @5
    wph
    @44
    @49
    @60
    caddc
    co
    #
    @5
    @12
    @49
    @19
    @60
    caddc
    @50
    @61
    oveq12i
    wph
    @2
    @68
    @5
    wceq
    #
    wph
    @2
    @69
    @27
    @48
    @59
    caddc
    co
    #
    @4
    @68
    @5
    @27
    @53
    @70
    @4
    wceq
    iblabs.5
    @3
    max0add
    syl
    @27
    @49
    @48
    @60
    @59
    caddc
    @2
    @49
    @48
    wceq
    wph
    @2
    @48
    cc0
    iftrue
    adantl
    @2
    @60
    @59
    wceq
    wph
    @2
    @59
    cc0
    iftrue
    adantl
    oveq12d
    @29
    3eqtr4d
    ex
    @33
    cc0
    cc0
    caddc
    co
    cc0
    @68
    @5
    00id
    @33
    @49
    cc0
    @60
    cc0
    caddc
    @2
    @48
    cc0
    iffalse
    #
    @2
    @59
    cc0
    iffalse
    #
    oveq12d
    @35
    3eqtr4a
    pm2.61d1
    syl5eq
    mpteq2dv
    eqtrd
    iblabs.3
    syl6reqr
    fveq2d
    wph
    @13
    @20
    wph
    vx
    cA
    cr
    @12
    @45
    @25
    @26
    wph
    @46
    @2
    @56
    adantr
    @32
    @33
    @12
    cc0
    wceq
    @34
    @33
    @12
    @49
    cc0
    @50
    @71
    syl5eq
    syl
    wph
    vx
    cA
    @12
    cmpt
    vx
    cA
    @48
    cmpt
    cmbf
    vx
    cA
    @48
    @12
    @2
    @10
    @11
    @3
    cc0
    @2
    @10
    ibar
    ifbid
    mpteq2ia
    wph
    vx
    cA
    @3
    iblabs.5
    @24
    mbfpos
    syl5eqelr
    mbfss
    wph
    vx
    cr
    @12
    @45
    @13
    @57
    @13
    eqid
    fmptd
    wph
    @9
    @15
    @22
    @23
    simp2d
    #
    wph
    vx
    cA
    cr
    @19
    @45
    @25
    @26
    wph
    @58
    @2
    @66
    adantr
    @32
    @33
    @19
    cc0
    wceq
    @34
    @33
    @19
    @60
    cc0
    @61
    @72
    syl5eq
    syl
    wph
    vx
    cA
    @19
    cmpt
    vx
    cA
    @59
    cmpt
    cmbf
    vx
    cA
    @59
    @19
    @2
    @17
    @18
    @16
    cc0
    @2
    @17
    ibar
    ifbid
    mpteq2ia
    wph
    vx
    cA
    @16
    @65
    wph
    vx
    cA
    @3
    cr
    iblabs.5
    @24
    mbfneg
    mbfpos
    syl5eqelr
    mbfss
    wph
    vx
    cr
    @19
    @45
    @20
    @67
    @20
    eqid
    fmptd
    wph
    @9
    @15
    @22
    @23
    simp3d
    #
    itg2add
    eqtrd
    wph
    @14
    @21
    @73
    @74
    readdcld
    eqeltrd
    jca
end
