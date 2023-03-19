include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "wf.mm"
include "caddc.mm"
include "citg2.mm"
include "cfv.mm"
include "ifan.mm"
include "cxr.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "rexrd.mm"
include "max1.mm"
include "sylancr.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "fmptd.mm"
include "cof.mm"
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "offval2.mm"
include "wceq.mm"
include "iftrue.mm"
include "ibar.mm"
include "ifbid.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "00id.mm"
include "simpl.mm"
include "con3i.mm"
include "iffalsed.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "syl.mm"
include "rembl.mm"
include "cdif.mm"
include "eldifn.mm"
include "adantl.mm"
include "intnanrd.mm"
include "cmbf.mm"
include "mpteq2ia.mm"
include "mbfpos.mm"
include "syl5eqelr.mm"
include "mbfss.mm"
include "cico.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "itg2add.mm"
include "eqtr3d.mm"
include "cofr.mm"
include "addge0d.mm"
include "wral.mm"
include "max2.mm"
include "le2addd.mm"
include "eqbrtrd.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "3brtr4d.mm"
include "ex.mm"
include "0le0.mm"
include "pm2.61d1.mm"
include "syl5eqbr.mm"
include "ralrimivw.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"

theorem ibladdlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ibladd.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume ibladd.2: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume ibladd.3: |- ( ( ph /\ x e. A ) -> D = ( B + C ) )
  assume ibladd.4: |- ( ph -> ( x e. A |-> B ) e. MblFn )
  assume ibladd.5: |- ( ph -> ( x e. A |-> C ) e. MblFn )
  assume ibladd.6: |- ( ph -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ B ) , B , 0 ) ) ) e. RR )
  assume ibladd.7: |- ( ph -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ C ) , C , 0 ) ) ) e. RR )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ D ) , D , 0 ) ) ) e. RR )

  proof
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    cD
    cle
    wbr
    #
    wa
    cD
    cc0
    cif
    #
    cmpt
    #
    wf
    #
    vx
    cr
    @2
    cc0
    cB
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    cc0
    cC
    cle
    wbr
    #
    cC
    cc0
    cif
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
    @5
    citg2
    cfv
    #
    @14
    cle
    wbr
    #
    @15
    cr
    wcel
    wph
    vx
    cr
    @4
    @0
    @5
    wph
    @1
    cr
    wcel
    #
    wa
    @4
    @2
    @3
    cD
    cc0
    cif
    #
    cc0
    cif
    #
    @0
    @2
    @3
    cD
    cc0
    ifan
    #
    wph
    @19
    @0
    wcel
    @17
    wph
    @2
    @18
    cc0
    @0
    wph
    @2
    wa
    #
    @18
    cxr
    wcel
    cc0
    @18
    cle
    wbr
    #
    @18
    @0
    wcel
    @21
    @18
    @21
    cD
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @18
    cr
    wcel
    @21
    cD
    cB
    cC
    caddc
    co
    #
    cr
    ibladd.3
    @21
    cB
    cC
    ibladd.1
    ibladd.2
    readdcld
    eqeltrd
    #
    0re
    @3
    cD
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @21
    @24
    @23
    @22
    0re
    @26
    cc0
    cD
    max1
    sylancr
    @18
    elxrge0
    sylanbrc
    cc0
    @0
    wcel
    wph
    @2
    wn
    #
    wa
    #
    0e0iccpnf
    a1i
    #
    ifclda
    adantr
    syl5eqel
    #
    @5
    eqid
    fmptd
    #
    wph
    @14
    vx
    cr
    @2
    @7
    wa
    #
    cB
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
    @2
    @9
    wa
    #
    cC
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
    @34
    @38
    caddc
    cof
    co
    #
    citg2
    cfv
    @14
    @40
    wph
    @41
    @13
    citg2
    wph
    @41
    vx
    cr
    @33
    @37
    caddc
    co
    #
    cmpt
    @13
    wph
    vx
    cr
    @33
    @37
    caddc
    @34
    @38
    cvv
    cr
    cr
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    wph
    @33
    cr
    wcel
    #
    @17
    wph
    @33
    @2
    @8
    cc0
    cif
    #
    cr
    @2
    @7
    cB
    cc0
    ifan
    #
    wph
    @2
    @8
    cc0
    cr
    @21
    cB
    cr
    wcel
    #
    @24
    @8
    cr
    wcel
    #
    ibladd.1
    0re
    @7
    cB
    cc0
    cr
    ifcl
    sylancl
    #
    @24
    @28
    0re
    a1i
    #
    ifclda
    syl5eqel
    #
    adantr
    wph
    @37
    cr
    wcel
    #
    @17
    wph
    @37
    @2
    @10
    cc0
    cif
    #
    cr
    @2
    @9
    cC
    cc0
    ifan
    #
    wph
    @2
    @10
    cc0
    cr
    @21
    cC
    cr
    wcel
    #
    @24
    @10
    cr
    wcel
    #
    ibladd.2
    0re
    @9
    cC
    cc0
    cr
    ifcl
    sylancl
    #
    @50
    ifclda
    syl5eqel
    #
    adantr
    wph
    @34
    eqidd
    wph
    @38
    eqidd
    offval2
    vx
    cr
    @42
    @12
    @2
    @42
    @12
    wceq
    @2
    @12
    @11
    @42
    @2
    @11
    cc0
    iftrue
    #
    @2
    @8
    @33
    @10
    @37
    caddc
    @2
    @7
    @32
    cB
    cc0
    @2
    @7
    ibar
    ifbid
    #
    @2
    @9
    @36
    cC
    cc0
    @2
    @9
    ibar
    ifbid
    #
    oveq12d
    eqtr2d
    @27
    cc0
    cc0
    caddc
    co
    cc0
    @42
    @12
    00id
    @27
    @33
    cc0
    @37
    cc0
    caddc
    @27
    @32
    cB
    cc0
    @32
    @2
    @2
    @7
    simpl
    con3i
    iffalsed
    @27
    @36
    cC
    cc0
    @36
    @2
    @2
    @9
    simpl
    con3i
    iffalsed
    #
    oveq12d
    @2
    @11
    cc0
    iffalse
    #
    3eqtr4a
    pm2.61i
    mpteq2i
    syl6eq
    fveq2d
    wph
    @34
    @38
    wph
    vx
    cA
    cr
    @33
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
    cB
    cr
    ibladd.4
    ibladd.1
    mbfdm2
    cA
    mblss
    syl
    #
    cr
    @64
    wcel
    wph
    rembl
    a1i
    #
    wph
    @44
    @2
    @51
    adantr
    wph
    @1
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    @32
    cB
    cc0
    @68
    @2
    @7
    @67
    @27
    wph
    @1
    cr
    cA
    eldifn
    adantl
    #
    intnanrd
    iffalsed
    wph
    vx
    cA
    @33
    cmpt
    vx
    cA
    @8
    cmpt
    cmbf
    vx
    cA
    @8
    @33
    @60
    mpteq2ia
    wph
    vx
    cA
    cB
    ibladd.1
    ibladd.4
    mbfpos
    syl5eqelr
    mbfss
    wph
    vx
    cr
    @33
    cc0
    cpnf
    cico
    co
    #
    @34
    wph
    @33
    @70
    wcel
    @17
    wph
    @33
    @45
    @70
    @46
    wph
    @2
    @8
    cc0
    @70
    @21
    @48
    cc0
    @8
    cle
    wbr
    #
    @8
    @70
    wcel
    @49
    @21
    @24
    @47
    @71
    0re
    ibladd.1
    cc0
    cB
    max1
    sylancr
    #
    @8
    elrege0
    sylanbrc
    cc0
    @70
    wcel
    @28
    0e0icopnf
    a1i
    #
    ifclda
    syl5eqel
    adantr
    @34
    eqid
    fmptd
    ibladd.6
    wph
    vx
    cA
    cr
    @37
    cr
    @65
    @66
    wph
    @52
    @2
    @58
    adantr
    @68
    @27
    @37
    cc0
    wceq
    @69
    @62
    syl
    wph
    vx
    cA
    @37
    cmpt
    vx
    cA
    @10
    cmpt
    cmbf
    vx
    cA
    @10
    @37
    @61
    mpteq2ia
    wph
    vx
    cA
    cC
    ibladd.2
    ibladd.5
    mbfpos
    syl5eqelr
    mbfss
    wph
    vx
    cr
    @37
    @70
    @38
    wph
    @37
    @70
    wcel
    @17
    wph
    @37
    @53
    @70
    @54
    wph
    @2
    @10
    cc0
    @70
    @21
    @56
    cc0
    @10
    cle
    wbr
    #
    @10
    @70
    wcel
    @57
    @21
    @24
    @55
    @74
    0re
    ibladd.2
    cc0
    cC
    max1
    sylancr
    #
    @10
    elrege0
    sylanbrc
    @73
    ifclda
    syl5eqel
    adantr
    @38
    eqid
    fmptd
    ibladd.7
    itg2add
    eqtr3d
    wph
    @35
    @39
    ibladd.6
    ibladd.7
    readdcld
    eqeltrd
    wph
    @6
    cr
    @0
    @13
    wf
    @5
    @13
    cle
    cofr
    wbr
    #
    @16
    @31
    wph
    vx
    cr
    @12
    @0
    @13
    wph
    @12
    @0
    wcel
    @17
    wph
    @2
    @11
    cc0
    @0
    @21
    @11
    cxr
    wcel
    cc0
    @11
    cle
    wbr
    #
    @11
    @0
    wcel
    @21
    @11
    @21
    @8
    @10
    @49
    @57
    readdcld
    rexrd
    @21
    @8
    @10
    @49
    @57
    @72
    @75
    addge0d
    #
    @11
    elxrge0
    sylanbrc
    @29
    ifclda
    adantr
    #
    @13
    eqid
    fmptd
    wph
    @76
    @4
    @12
    cle
    wbr
    #
    vx
    cr
    wral
    wph
    @80
    vx
    cr
    wph
    @4
    @19
    @12
    cle
    @20
    wph
    @2
    @19
    @12
    cle
    wbr
    #
    wph
    @2
    @81
    @21
    @18
    @11
    @19
    @12
    cle
    @21
    cD
    @11
    cle
    wbr
    #
    @77
    @18
    @11
    cle
    wbr
    #
    @21
    cD
    @25
    @11
    cle
    ibladd.3
    @21
    cB
    cC
    @8
    @10
    ibladd.1
    ibladd.2
    @49
    @57
    @21
    @24
    @47
    cB
    @8
    cle
    wbr
    0re
    ibladd.1
    cc0
    cB
    max2
    sylancr
    @21
    @24
    @55
    cC
    @10
    cle
    wbr
    0re
    ibladd.2
    cc0
    cC
    max2
    sylancr
    le2addd
    eqbrtrd
    @78
    @3
    @82
    @77
    @83
    cD
    cc0
    cD
    @18
    @11
    cle
    breq1
    cc0
    @18
    @11
    cle
    breq1
    ifboth
    syl2anc
    @2
    @19
    @18
    wceq
    wph
    @2
    @18
    cc0
    iftrue
    adantl
    @2
    @12
    @11
    wceq
    wph
    @59
    adantl
    3brtr4d
    ex
    @27
    cc0
    cc0
    @19
    @12
    cle
    cc0
    cc0
    cle
    wbr
    @27
    0le0
    a1i
    @2
    @18
    cc0
    iffalse
    @63
    3brtr4d
    pm2.61d1
    syl5eqbr
    ralrimivw
    wph
    vx
    cr
    @4
    @12
    cle
    @5
    @13
    cvv
    @0
    @0
    @43
    @30
    @79
    wph
    @5
    eqidd
    wph
    @13
    eqidd
    ofrfval2
    mpbird
    @5
    @13
    itg2le
    syl3anc
    @14
    @5
    itg2lecl
    syl3anc
end
