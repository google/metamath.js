include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "cc.mm"
include "eqid.mm"
include "fmptd.mm"
include "cres.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "resmptd.mm"
include "eqidd.mm"
include "sseld.mm"
include "imdistani.mm"
include "syl.mm"
include "isibl2.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "ssun2.mm"
include "eqcomd.mm"
include "mbfres2cn.mm"
include "caddc.mm"
include "cvol.mm"
include "cdm.mm"
include "mbfdm2.mm"
include "adantr.mm"
include "cin.mm"
include "covol.mm"
include "wceq.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "adantlr.mm"
include "ax-icn.mm"
include "a1i.mm"
include "elfznn0.mm"
include "expcld.mm"
include "ad2antlr.mm"
include "wne.mm"
include "ine0.mm"
include "cz.mm"
include "elfzelz.mm"
include "expne0d.mm"
include "divcld.mm"
include "recld.mm"
include "rexrd.mm"
include "simpr.mm"
include "pnfge.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "ifclda.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "eqcomi.mm"
include "fveq2d.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "fveq2i.mm"
include "syl5eqel.mm"
include "itg2split.mm"
include "readdcld.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem iblsplit
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  let vy: setvar y
  assume iblsplit.1: |- ( ph -> ( vol* ` ( A i^i B ) ) = 0 )
  assume iblsplit.2: |- ( ph -> U = ( A u. B ) )
  assume iblsplit.3: |- ( ( ph /\ x e. U ) -> C e. CC )
  assume iblsplit.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume iblsplit.5: |- ( ph -> ( x e. B |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint U x
  disjoint ph x
  disjoint A k
  disjoint k x
  disjoint A y
  disjoint x y
  disjoint B k
  disjoint B y
  disjoint C k
  disjoint C y
  disjoint U k
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( x e. U |-> C ) e. L^1 )

  proof
    wph
    vx
    cU
    cC
    cmpt
    #
    cibl
    wcel
    @0
    cmbf
    wcel
    vx
    cr
    vx
    cv
    #
    cU
    wcel
    #
    cc0
    cC
    ci
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    @6
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
    vk
    cc0
    c3
    cfz
    co
    #
    wral
    wph
    cU
    cA
    cB
    @0
    wph
    vx
    cU
    cC
    cc
    @0
    iblsplit.3
    @0
    eqid
    fmptd
    wph
    @0
    cA
    cres
    vx
    cA
    cC
    cmpt
    #
    cmbf
    wph
    vx
    cU
    cA
    cC
    wph
    cA
    cB
    cun
    #
    cA
    cU
    cA
    cB
    ssun1
    iblsplit.2
    syl5sseqr
    #
    resmptd
    wph
    @13
    cmbf
    wcel
    #
    vx
    cr
    @1
    cA
    wcel
    #
    cc0
    cC
    ci
    vy
    cv
    cexp
    co
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    @18
    cc0
    cif
    cmpt
    #
    citg2
    cfv
    cr
    wcel
    vy
    @12
    wral
    #
    wph
    @13
    cibl
    wcel
    #
    @16
    @21
    wa
    iblsplit.4
    wph
    vx
    cA
    cC
    @18
    vy
    @20
    cc
    wph
    @20
    eqidd
    wph
    @17
    wa
    #
    @18
    eqidd
    @23
    wph
    @2
    wa
    #
    cC
    cc
    wcel
    #
    wph
    @17
    @2
    wph
    cA
    cU
    @1
    @15
    sseld
    imdistani
    iblsplit.3
    syl
    #
    isibl2
    mpbid
    simpld
    #
    eqeltrd
    wph
    @0
    cB
    cres
    vx
    cB
    cC
    cmpt
    #
    cmbf
    wph
    vx
    cU
    cB
    cC
    wph
    @14
    cB
    cU
    cB
    cA
    ssun2
    iblsplit.2
    syl5sseqr
    #
    resmptd
    wph
    @28
    cmbf
    wcel
    #
    vx
    cr
    @1
    cB
    wcel
    #
    @19
    wa
    @18
    cc0
    cif
    cmpt
    #
    citg2
    cfv
    cr
    wcel
    vy
    @12
    wral
    #
    wph
    @28
    cibl
    wcel
    #
    @30
    @33
    wa
    iblsplit.5
    wph
    vx
    cB
    cC
    @18
    vy
    @32
    cc
    wph
    @32
    eqidd
    wph
    @31
    wa
    #
    @18
    eqidd
    @35
    @24
    @25
    wph
    @31
    @2
    wph
    cB
    cU
    @1
    @29
    sseld
    imdistani
    iblsplit.3
    syl
    #
    isibl2
    mpbid
    simpld
    #
    eqeltrd
    wph
    cU
    @14
    iblsplit.2
    eqcomd
    mbfres2cn
    wph
    @11
    vk
    @12
    wph
    @3
    @12
    wcel
    #
    wa
    #
    @10
    vx
    cr
    @17
    @7
    @6
    cc0
    cif
    #
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
    @31
    @40
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
    cr
    @39
    vx
    cA
    cB
    @40
    cU
    @42
    @45
    @9
    wph
    cA
    cvol
    cdm
    #
    wcel
    @38
    wph
    vx
    cA
    cC
    cc
    @27
    @26
    mbfdm2
    adantr
    wph
    cB
    @47
    wcel
    @38
    wph
    vx
    cB
    cC
    cc
    @37
    @36
    mbfdm2
    adantr
    wph
    cA
    cB
    cin
    covol
    cfv
    cc0
    wceq
    @38
    iblsplit.1
    adantr
    wph
    cU
    @14
    wceq
    @38
    iblsplit.2
    adantr
    @39
    @2
    wa
    #
    @7
    @6
    cc0
    cc0
    cpnf
    cicc
    co
    #
    @48
    @7
    wa
    #
    @6
    cxr
    wcel
    #
    @7
    @6
    cpnf
    cle
    wbr
    #
    @6
    @49
    wcel
    #
    @48
    @51
    @7
    @48
    @6
    @48
    @5
    @48
    cC
    @4
    wph
    @2
    @25
    @38
    iblsplit.3
    adantlr
    @38
    @4
    cc
    wcel
    wph
    @2
    @38
    ci
    @3
    ci
    cc
    wcel
    #
    @38
    ax-icn
    a1i
    @3
    c3
    elfznn0
    expcld
    ad2antlr
    @48
    ci
    @3
    @54
    @48
    ax-icn
    a1i
    ci
    cc0
    wne
    @48
    ine0
    a1i
    @38
    @3
    cz
    wcel
    wph
    @2
    @3
    cc0
    c3
    elfzelz
    ad2antlr
    expne0d
    divcld
    recld
    rexrd
    adantr
    #
    @48
    @7
    simpr
    @50
    @51
    @52
    @55
    @6
    pnfge
    syl
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @53
    @51
    @7
    @52
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @6
    elicc1
    mp2an
    syl3anbrc
    cc0
    @49
    wcel
    @48
    @7
    wn
    wa
    0e0iccpnf
    a1i
    ifclda
    @42
    eqid
    @45
    eqid
    vx
    cr
    @8
    @2
    @40
    cc0
    cif
    @2
    @7
    @6
    cc0
    ifan
    mpteq2i
    @39
    @43
    vx
    cr
    @17
    @7
    wa
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @39
    @42
    @57
    citg2
    @42
    @57
    wceq
    @39
    vx
    cr
    @41
    @56
    @56
    @41
    @17
    @7
    @6
    cc0
    ifan
    eqcomi
    mpteq2i
    a1i
    fveq2d
    wph
    @58
    cr
    wcel
    #
    vk
    @12
    wph
    @16
    @59
    vk
    @12
    wral
    #
    wph
    @22
    @16
    @60
    wa
    iblsplit.4
    wph
    vx
    cA
    cC
    @6
    vk
    @57
    cc
    wph
    @57
    eqidd
    @23
    @6
    eqidd
    @26
    isibl2
    mpbid
    simprd
    r19.21bi
    eqeltrd
    #
    @39
    @46
    vx
    cr
    @31
    @7
    wa
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @45
    @63
    citg2
    vx
    cr
    @44
    @62
    @62
    @44
    @31
    @7
    @6
    cc0
    ifan
    eqcomi
    mpteq2i
    fveq2i
    wph
    @64
    cr
    wcel
    #
    vk
    @12
    wph
    @30
    @65
    vk
    @12
    wral
    #
    wph
    @34
    @30
    @66
    wa
    iblsplit.5
    wph
    vx
    cB
    cC
    @6
    vk
    @63
    cc
    wph
    @63
    eqidd
    @35
    @6
    eqidd
    @36
    isibl2
    mpbid
    simprd
    r19.21bi
    syl5eqel
    #
    itg2split
    @39
    @43
    @46
    @61
    @67
    readdcld
    eqeltrd
    ralrimiva
    wph
    vx
    cU
    cC
    @6
    vk
    @9
    cc
    wph
    @9
    eqidd
    @24
    @6
    eqidd
    iblsplit.3
    isibl2
    mpbir2and
end
