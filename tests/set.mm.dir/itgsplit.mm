include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "caddc.mm"
include "citg.mm"
include "cvol.mm"
include "cdm.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "mbfdm2.mm"
include "adantr.mm"
include "ssun2.mm"
include "cin.mm"
include "covol.mm"
include "wceq.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "cc.mm"
include "wo.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "mbfmptcl.mm"
include "jaodan.mm"
include "adantlr.mm"
include "cn0.mm"
include "ax-icn.mm"
include "elfznn0.mm"
include "adantl.mm"
include "expcl.mm"
include "sylancr.mm"
include "wne.mm"
include "cz.mm"
include "elfzelz.mm"
include "ine0.mm"
include "expne0i.mm"
include "mp3an12.mm"
include "divcld.mm"
include "recld.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "rexrd.mm"
include "max1.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "eqidd.mm"
include "iblitg.mm"
include "sylan2.mm"
include "itg2split.mm"
include "oveq2d.mm"
include "recnd.mm"
include "adddid.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "mulcld.mm"
include "fsumadd.mm"
include "eqid.mm"
include "dfitg.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem itgsplit
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vk: setvar k
  assume itgsplit.i: |- ( ph -> ( vol* ` ( A i^i B ) ) = 0 )
  assume itgsplit.u: |- ( ph -> U = ( A u. B ) )
  assume itgsplit.c: |- ( ( ph /\ x e. U ) -> C e. V )
  assume itgsplit.a: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume itgsplit.b: |- ( ph -> ( x e. B |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint U x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint k ph
  disjoint U k
  assert |- ( ph -> S. U C _d x = ( S. A C _d x + S. B C _d x ) )

  proof
    wph
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
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
    @2
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
    cmul
    co
    #
    vk
    csu
    #
    @0
    @2
    vx
    cr
    @3
    cA
    wcel
    #
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
    cmul
    co
    #
    vk
    csu
    #
    @0
    @2
    vx
    cr
    @3
    cB
    wcel
    #
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
    cmul
    co
    #
    vk
    csu
    #
    caddc
    co
    #
    vx
    cU
    cC
    citg
    vx
    cA
    cC
    citg
    #
    vx
    cB
    cC
    citg
    #
    caddc
    co
    wph
    @12
    @0
    @17
    @23
    caddc
    co
    #
    vk
    csu
    @25
    wph
    @0
    @11
    @28
    vk
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @11
    @2
    @16
    @22
    caddc
    co
    #
    cmul
    co
    @28
    @30
    @10
    @31
    @2
    cmul
    @30
    vx
    cA
    cB
    @7
    @6
    cc0
    cif
    #
    cU
    @15
    @21
    @9
    wph
    cA
    cvol
    cdm
    #
    wcel
    @29
    wph
    vx
    cA
    cC
    cV
    wph
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    @34
    cmbf
    wcel
    itgsplit.a
    @34
    iblmbf
    syl
    #
    wph
    @13
    @4
    cC
    cV
    wcel
    #
    wph
    cA
    cU
    @3
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
    itgsplit.u
    syl5sseqr
    sselda
    itgsplit.c
    syldan
    #
    mbfdm2
    adantr
    wph
    cB
    @33
    wcel
    @29
    wph
    vx
    cB
    cC
    cV
    wph
    vx
    cB
    cC
    cmpt
    #
    cibl
    wcel
    @39
    cmbf
    wcel
    itgsplit.b
    @39
    iblmbf
    syl
    #
    wph
    @19
    @4
    @36
    wph
    cB
    cU
    @3
    wph
    @37
    cB
    cU
    cB
    cA
    ssun2
    itgsplit.u
    syl5sseqr
    sselda
    itgsplit.c
    syldan
    #
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
    @29
    itgsplit.i
    adantr
    wph
    cU
    @37
    wceq
    @29
    itgsplit.u
    adantr
    @30
    @4
    wa
    #
    @32
    cxr
    wcel
    cc0
    @32
    cle
    wbr
    #
    @32
    cc0
    cpnf
    cicc
    co
    wcel
    @42
    @32
    @42
    @6
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @32
    cr
    wcel
    @42
    @5
    @42
    cC
    @2
    wph
    @4
    cC
    cc
    wcel
    #
    @29
    wph
    @4
    @13
    @19
    wo
    #
    @46
    wph
    @4
    @47
    wph
    @4
    @3
    @37
    wcel
    @47
    wph
    cU
    @37
    @3
    itgsplit.u
    eleq2d
    @3
    cA
    cB
    elun
    syl6bb
    biimpa
    wph
    @13
    @46
    @19
    wph
    vx
    cA
    cC
    cV
    @35
    @38
    mbfmptcl
    wph
    vx
    cB
    cC
    cV
    @40
    @41
    mbfmptcl
    jaodan
    syldan
    adantlr
    @30
    @2
    cc
    wcel
    #
    @4
    @30
    ci
    cc
    wcel
    #
    @1
    cn0
    wcel
    #
    @48
    ax-icn
    @29
    @50
    wph
    @1
    c3
    elfznn0
    adantl
    ci
    @1
    expcl
    sylancr
    #
    adantr
    @30
    @2
    cc0
    wne
    #
    @4
    @30
    @1
    cz
    wcel
    #
    @52
    @29
    @53
    wph
    @1
    cc0
    c3
    elfzelz
    #
    adantl
    @49
    ci
    cc0
    wne
    @53
    @52
    ax-icn
    ine0
    ci
    @1
    expne0i
    mp3an12
    syl
    adantr
    divcld
    recld
    #
    0re
    @7
    @6
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @42
    @45
    @44
    @43
    0re
    @55
    cc0
    @6
    max1
    sylancr
    @32
    elxrge0
    sylanbrc
    vx
    cr
    @14
    @13
    @32
    cc0
    cif
    @13
    @7
    @6
    cc0
    ifan
    mpteq2i
    vx
    cr
    @20
    @19
    @32
    cc0
    cif
    @19
    @7
    @6
    cc0
    ifan
    mpteq2i
    vx
    cr
    @8
    @4
    @32
    cc0
    cif
    @4
    @7
    @6
    cc0
    ifan
    mpteq2i
    @29
    wph
    @53
    @16
    cr
    wcel
    @54
    wph
    vx
    cA
    cC
    @6
    @15
    @1
    cV
    wph
    @15
    eqidd
    wph
    @13
    wa
    @6
    eqidd
    itgsplit.a
    @38
    iblitg
    #
    sylan2
    @29
    wph
    @53
    @22
    cr
    wcel
    @54
    wph
    vx
    cB
    cC
    @6
    @21
    @1
    cV
    wph
    @21
    eqidd
    wph
    @19
    wa
    @6
    eqidd
    itgsplit.b
    @41
    iblitg
    sylan2
    #
    itg2split
    oveq2d
    @30
    @2
    @16
    @22
    @51
    @29
    wph
    @53
    @16
    cc
    wcel
    @54
    wph
    @53
    wa
    @16
    @56
    recnd
    sylan2
    #
    @30
    @22
    @57
    recnd
    #
    adddid
    eqtrd
    sumeq2dv
    wph
    @0
    @17
    @23
    vk
    wph
    cc0
    c3
    fzfid
    @30
    @2
    @16
    @51
    @58
    mulcld
    @30
    @2
    @22
    @51
    @59
    mulcld
    fsumadd
    eqtrd
    vx
    cU
    cC
    @6
    vk
    @6
    eqid
    #
    dfitg
    @26
    @18
    @27
    @24
    caddc
    vx
    cA
    cC
    @6
    vk
    @60
    dfitg
    vx
    cB
    cC
    @6
    vk
    @60
    dfitg
    oveq12i
    3eqtr4g
end
