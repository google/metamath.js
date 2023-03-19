include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "cicc.mm"
include "cprime.mm"
include "cin.mm"
include "clog.mm"
include "cv.mm"
include "cdiv.mm"
include "fzfid.mm"
include "cn.mm"
include "wss.mm"
include "elfznn.mm"
include "ssriv.mm"
include "a1i.mm"
include "cr.mm"
include "wcel.mm"
include "cfn.mm"
include "ppifi.mm"
include "syl.mm"
include "wa.mm"
include "cexp.mm"
include "elin.mm"
include "simprbi.mm"
include "anim12i.mm"
include "pm4.71ri.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "wb.mm"
include "adantr.mm"
include "prmnn.mm"
include "ad2antrl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "flge.mm"
include "syl2anc.mm"
include "cmul.mm"
include "crp.mm"
include "wceq.mm"
include "simplrl.mm"
include "nnrpd.mm"
include "simplrr.mm"
include "relogexp.mm"
include "breq1d.mm"
include "nnred.mm"
include "0red.mm"
include "nngt0d.mm"
include "nn0ge0d.mm"
include "w3a.mm"
include "elicc2.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl22anc.mm"
include "biimpa.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "relogcld.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzelre.mm"
include "clt.mm"
include "eluz2b2.mm"
include "rplogcld.mm"
include "3syl.mm"
include "lemuldivd.mm"
include "rerpdivcld.mm"
include "3bitrd.mm"
include "logled.mm"
include "simprr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "flcld.mm"
include "elfz5.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "nncnd.mm"
include "exp1d.mm"
include "nnge1d.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "wi.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylibrd.mm"
include "pm4.71rd.mm"
include "rbaib.mm"
include "anbi1d.mm"
include "3bitr4rd.mm"
include "syl5bb.mm"
include "fsumvma.mm"

theorem fsumvma2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vp: setvar p
  assume fsumvma2.1: |- ( x = ( p ^ k ) -> B = C )
  assume fsumvma2.2: |- ( ph -> A e. RR )
  assume fsumvma2.3: |- ( ( ph /\ x e. ( 1 ... ( |_ ` A ) ) ) -> B e. CC )
  assume fsumvma2.4: |- ( ( ph /\ ( x e. ( 1 ... ( |_ ` A ) ) /\ ( Lam ` x ) = 0 ) ) -> B = 0 )

  disjoint k p
  disjoint k x
  disjoint A k
  disjoint p x
  disjoint A p
  disjoint A x
  disjoint C x
  disjoint k ph
  disjoint p ph
  disjoint ph x
  disjoint B k
  disjoint B p
  assert |- ( ph -> sum_ x e. ( 1 ... ( |_ ` A ) ) B = sum_ p e. ( ( 0 [,] A ) i^i Prime ) sum_ k e. ( 1 ... ( |_ ` ( ( log ` A ) / ( log ` p ) ) ) ) C )

  proof
    wph
    vx
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cB
    cC
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    vk
    c1
    cA
    clog
    cfv
    #
    vp
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vp
    fsumvma2.1
    wph
    c1
    @0
    fzfid
    @1
    cn
    wss
    wph
    vx
    @1
    cn
    vx
    cv
    @0
    elfznn
    ssriv
    a1i
    wph
    cA
    cr
    wcel
    #
    @3
    cfn
    wcel
    fsumvma2.2
    cA
    ppifi
    syl
    @5
    @3
    wcel
    #
    vk
    cv
    #
    @9
    wcel
    #
    wa
    #
    @5
    cprime
    wcel
    #
    @12
    cn
    wcel
    #
    wa
    #
    @14
    wa
    wph
    @17
    @5
    @12
    cexp
    co
    #
    @1
    wcel
    #
    wa
    @14
    @17
    @11
    @15
    @13
    @16
    @11
    @5
    @2
    wcel
    #
    @15
    @5
    @2
    cprime
    elin
    #
    simprbi
    @12
    @8
    elfznn
    anim12i
    pm4.71ri
    wph
    @17
    @14
    @19
    wph
    @17
    wa
    #
    @18
    cA
    cle
    wbr
    #
    @18
    @0
    cle
    wbr
    #
    @14
    @19
    @22
    @10
    @18
    cz
    wcel
    @23
    @24
    wb
    wph
    @10
    @17
    fsumvma2.2
    adantr
    #
    @22
    @18
    @22
    @5
    @12
    @15
    @5
    cn
    wcel
    #
    wph
    @16
    @5
    prmnn
    #
    ad2antrl
    #
    @16
    @12
    cn0
    wcel
    wph
    @15
    @12
    nnnn0
    ad2antll
    nnexpcld
    #
    nnzd
    cA
    @18
    flge
    syl2anc
    @22
    @20
    @23
    wa
    @20
    @13
    wa
    @23
    @14
    @22
    @20
    @23
    @13
    @22
    @20
    wa
    #
    @18
    clog
    cfv
    #
    @4
    cle
    wbr
    #
    @12
    @8
    cle
    wbr
    #
    @23
    @13
    @30
    @32
    @12
    @6
    cmul
    co
    #
    @4
    cle
    wbr
    @12
    @7
    cle
    wbr
    #
    @33
    @30
    @31
    @34
    @4
    cle
    @30
    @5
    crp
    wcel
    @12
    cz
    wcel
    #
    @31
    @34
    wceq
    @30
    @5
    @30
    @15
    @26
    wph
    @15
    @16
    @20
    simplrl
    #
    @27
    syl
    #
    nnrpd
    @30
    @12
    wph
    @15
    @16
    @20
    simplrr
    #
    nnzd
    #
    @5
    @12
    relogexp
    syl2anc
    breq1d
    @30
    @12
    @4
    @6
    @30
    @12
    @39
    nnred
    @30
    cA
    @30
    cA
    @22
    @10
    @20
    @25
    adantr
    #
    @30
    cc0
    @5
    cA
    @30
    0red
    @22
    @5
    cr
    wcel
    #
    @20
    @22
    @5
    @28
    nnred
    #
    adantr
    @41
    @30
    @5
    @38
    nngt0d
    @22
    @20
    @5
    cA
    cle
    wbr
    #
    @22
    cc0
    cr
    wcel
    #
    @10
    @42
    cc0
    @5
    cle
    wbr
    #
    @20
    @44
    wb
    @22
    0red
    @25
    @43
    @22
    @5
    @22
    @26
    @5
    cn0
    wcel
    @28
    @5
    nnnn0
    syl
    nn0ge0d
    @45
    @10
    wa
    #
    @20
    @42
    @46
    wa
    #
    @44
    @47
    @20
    @42
    @46
    @44
    w3a
    @48
    @44
    wa
    cc0
    cA
    @5
    elicc2
    @42
    @46
    @44
    df-3an
    syl6bb
    baibd
    syl22anc
    #
    biimpa
    ltletrd
    elrpd
    #
    relogcld
    #
    @30
    @15
    @5
    c2
    cuz
    cfv
    wcel
    #
    @6
    crp
    wcel
    @37
    @5
    prmuz2
    @52
    @5
    c2
    @5
    eluzelre
    @52
    @26
    c1
    @5
    clt
    wbr
    @5
    eluz2b2
    simprbi
    rplogcld
    3syl
    #
    lemuldivd
    @30
    @7
    cr
    wcel
    @36
    @35
    @33
    wb
    @30
    @4
    @6
    @51
    @53
    rerpdivcld
    #
    @40
    @7
    @12
    flge
    syl2anc
    3bitrd
    @30
    @18
    cA
    @30
    @18
    @22
    @18
    cn
    wcel
    @20
    @29
    adantr
    nnrpd
    @50
    logled
    @30
    @12
    c1
    cuz
    cfv
    #
    wcel
    #
    @8
    cz
    wcel
    @13
    @33
    wb
    @22
    @56
    @20
    @22
    @12
    cn
    @55
    wph
    @15
    @16
    simprr
    nnuz
    syl6eleq
    #
    adantr
    @30
    @7
    @54
    flcld
    @12
    c1
    @8
    elfz5
    syl2anc
    3bitr4d
    pm5.32da
    @22
    @23
    @20
    @22
    @23
    @44
    @20
    @22
    @5
    @18
    cle
    wbr
    #
    @23
    @44
    @22
    @5
    c1
    cexp
    co
    @5
    @18
    cle
    @22
    @5
    @22
    @5
    @28
    nncnd
    exp1d
    @22
    @5
    c1
    @12
    @43
    @22
    @5
    @28
    nnge1d
    @57
    leexp2ad
    eqbrtrrd
    @22
    @42
    @18
    cr
    wcel
    @10
    @58
    @23
    wa
    @44
    wi
    @43
    @22
    @18
    @29
    nnred
    @25
    @5
    @18
    cA
    letr
    syl3anc
    mpand
    @49
    sylibrd
    pm4.71rd
    @22
    @11
    @20
    @13
    @15
    @11
    @20
    wb
    wph
    @16
    @11
    @20
    @15
    @21
    rbaib
    ad2antrl
    anbi1d
    3bitr4rd
    @22
    @18
    @55
    wcel
    @0
    cz
    wcel
    @19
    @24
    wb
    @22
    @18
    cn
    @55
    @29
    nnuz
    syl6eleq
    @22
    cA
    @25
    flcld
    @18
    c1
    @0
    elfz5
    syl2anc
    3bitr4d
    pm5.32da
    syl5bb
    fsumvma2.3
    fsumvma2.4
    fsumvma
end
