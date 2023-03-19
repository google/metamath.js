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
include "w3a.mm"
include "cc.mm"
include "eqidd.mm"
include "isibl2.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c0ex.mm"
include "1ex.mm"
include "wceq.mm"
include "ax-icn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "itgvallem.mm"
include "eleq1d.mm"
include "exp1.mm"
include "ralpr.mm"
include "div1d.mm"
include "fveq2d.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "cim.mm"
include "imval.mm"
include "syl.mm"
include "syl5req.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "cneg.mm"
include "2ex.mm"
include "3ex.mm"
include "i2.mm"
include "i3.mm"
include "renegd.mm"
include "ax-1cn.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "negcld.mm"
include "syl5eq.mm"
include "wne.mm"
include "negcli.mm"
include "neg1ne0.mm"
include "div2neg.mm"
include "mp3an23.mm"
include "eqtr3d.mm"
include "imnegd.mm"
include "eqcomi.mm"
include "ine0.mm"
include "negne0i.mm"
include "3eqtr3d.mm"
include "cun.mm"
include "caddc.mm"
include "1le3.mm"
include "cuz.mm"
include "cz.mm"
include "wb.mm"
include "1eluzge0.mm"
include "3z.mm"
include "elfz5.mm"
include "mp2an.mm"
include "mpbir.mm"
include "fzsplit.mm"
include "0z.mm"
include "fzpr.mm"
include "1e0p1.mm"
include "preq2i.mm"
include "3eqtr4i.mm"
include "2z.mm"
include "1p1e2.mm"
include "df-3.mm"
include "oveq12i.mm"
include "uneq12i.mm"
include "eqtri.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "an4.mm"
include "3bitr4g.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem iblcnlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cV: class V
  assume itgcnlem.r: |- R = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Re ` B ) ) , ( Re ` B ) , 0 ) ) )
  assume itgcnlem.s: |- S = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Re ` B ) ) , -u ( Re ` B ) , 0 ) ) )
  assume itgcnlem.t: |- T = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Im ` B ) ) , ( Im ` B ) , 0 ) ) )
  assume itgcnlem.u: |- U = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Im ` B ) ) , -u ( Im ` B ) , 0 ) ) )
  assume itgcnlem1.v: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint A x
  disjoint ph x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint V x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> B ) e. MblFn /\ ( R e. RR /\ S e. RR ) /\ ( T e. RR /\ U e. RR ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @0
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    ci
    vk
    cv
    #
    cexp
    co
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    wa
    @4
    cc0
    cif
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
    #
    wa
    #
    @1
    cR
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    wa
    #
    cT
    cr
    wcel
    #
    cU
    cr
    wcel
    #
    wa
    #
    w3a
    #
    wph
    vx
    cA
    cB
    @4
    vk
    @5
    cc
    wph
    @5
    eqidd
    wph
    @2
    wa
    #
    @4
    eqidd
    itgcnlem1.v
    isibl2
    wph
    @10
    @1
    @13
    @16
    wa
    #
    wa
    @17
    wph
    @9
    @19
    @1
    wph
    @7
    vk
    cc0
    c1
    cpr
    #
    wral
    #
    @7
    vk
    c2
    c3
    cpr
    #
    wral
    #
    wa
    #
    @11
    @14
    wa
    #
    @12
    @15
    wa
    #
    wa
    @9
    @19
    wph
    @21
    @25
    @23
    @26
    @21
    vx
    cr
    @2
    cc0
    cB
    c1
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @28
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
    cB
    ci
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    wa
    @33
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
    wa
    wph
    @25
    @7
    @32
    @37
    vk
    cc0
    c1
    c0ex
    1ex
    @3
    cc0
    wceq
    @6
    @31
    cr
    vx
    cA
    cB
    c1
    vk
    cc0
    ci
    cc
    wcel
    #
    ci
    cc0
    cexp
    co
    c1
    wceq
    ax-icn
    ci
    exp0
    ax-mp
    itgvallem
    eleq1d
    @3
    c1
    wceq
    @6
    @36
    cr
    vx
    cA
    cB
    ci
    vk
    c1
    @38
    ci
    c1
    cexp
    co
    ci
    wceq
    ax-icn
    ci
    exp1
    ax-mp
    itgvallem
    eleq1d
    ralpr
    wph
    @32
    @11
    @37
    @14
    wph
    @31
    cR
    cr
    wph
    @31
    vx
    cr
    @2
    cc0
    cB
    cre
    cfv
    #
    cle
    wbr
    wa
    @39
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cR
    wph
    @30
    @41
    citg2
    wph
    vx
    cr
    @29
    @40
    wph
    vx
    cA
    @28
    @39
    @18
    @27
    cB
    cre
    @18
    cB
    itgcnlem1.v
    div1d
    fveq2d
    ibllem
    mpteq2dv
    fveq2d
    itgcnlem.r
    syl6eqr
    eleq1d
    wph
    @36
    cT
    cr
    wph
    cT
    vx
    cr
    @2
    cc0
    cB
    cim
    cfv
    #
    cle
    wbr
    wa
    @42
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @36
    itgcnlem.t
    wph
    @44
    @35
    citg2
    wph
    vx
    cr
    @43
    @34
    wph
    vx
    cA
    @42
    @33
    @18
    cB
    cc
    wcel
    #
    @42
    @33
    wceq
    itgcnlem1.v
    cB
    imval
    syl
    ibllem
    mpteq2dv
    fveq2d
    syl5req
    eleq1d
    anbi12d
    syl5bb
    @23
    vx
    cr
    @2
    cc0
    cB
    c1
    cneg
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @48
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
    cB
    ci
    cneg
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @55
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
    wa
    wph
    @26
    @7
    @52
    @59
    vk
    c2
    c3
    2ex
    3ex
    @3
    c2
    wceq
    @6
    @51
    cr
    vx
    cA
    cB
    @46
    vk
    c2
    i2
    itgvallem
    eleq1d
    @3
    c3
    wceq
    @6
    @58
    cr
    vx
    cA
    cB
    @53
    vk
    c3
    i3
    itgvallem
    eleq1d
    ralpr
    wph
    @52
    @12
    @59
    @15
    wph
    @51
    cS
    cr
    wph
    cS
    vx
    cr
    @2
    cc0
    @39
    cneg
    #
    cle
    wbr
    wa
    @60
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @51
    itgcnlem.s
    wph
    @62
    @50
    citg2
    wph
    vx
    cr
    @61
    @49
    wph
    vx
    cA
    @60
    @48
    @18
    cB
    cneg
    #
    cre
    cfv
    @60
    @48
    @18
    cB
    itgcnlem1.v
    renegd
    @18
    @63
    @47
    cre
    @18
    @63
    @46
    cneg
    #
    cdiv
    co
    #
    @63
    @47
    @18
    @65
    @63
    c1
    cdiv
    co
    @63
    @64
    c1
    @63
    cdiv
    c1
    ax-1cn
    negnegi
    oveq2i
    @18
    @63
    @18
    cB
    itgcnlem1.v
    negcld
    #
    div1d
    syl5eq
    @18
    @45
    @65
    @47
    wceq
    #
    itgcnlem1.v
    @45
    @46
    cc
    wcel
    @46
    cc0
    wne
    @67
    c1
    ax-1cn
    negcli
    neg1ne0
    cB
    @46
    div2neg
    mp3an23
    syl
    eqtr3d
    fveq2d
    eqtr3d
    ibllem
    mpteq2dv
    fveq2d
    syl5req
    eleq1d
    wph
    @58
    cU
    cr
    wph
    cU
    vx
    cr
    @2
    cc0
    @42
    cneg
    #
    cle
    wbr
    wa
    @68
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @58
    itgcnlem.u
    wph
    @70
    @57
    citg2
    wph
    vx
    cr
    @69
    @56
    wph
    vx
    cA
    @68
    @55
    @18
    @63
    cim
    cfv
    #
    @63
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    @68
    @55
    @18
    @63
    cc
    wcel
    @71
    @73
    wceq
    @66
    @63
    imval
    syl
    @18
    cB
    itgcnlem1.v
    imnegd
    @18
    @72
    @54
    cre
    @18
    @72
    @63
    @53
    cneg
    #
    cdiv
    co
    #
    @54
    ci
    @74
    @63
    cdiv
    @74
    ci
    ci
    ax-icn
    negnegi
    eqcomi
    oveq2i
    @18
    @45
    @75
    @54
    wceq
    #
    itgcnlem1.v
    @45
    @53
    cc
    wcel
    @53
    cc0
    wne
    @76
    ci
    ax-icn
    negcli
    ci
    ax-icn
    ine0
    negne0i
    cB
    @53
    div2neg
    mp3an23
    syl
    syl5eq
    fveq2d
    3eqtr3d
    ibllem
    mpteq2dv
    fveq2d
    syl5req
    eleq1d
    anbi12d
    syl5bb
    anbi12d
    @9
    @7
    vk
    @20
    @22
    cun
    #
    wral
    @24
    @7
    vk
    @8
    @77
    @8
    cc0
    c1
    cfz
    co
    #
    c1
    c1
    caddc
    co
    #
    c3
    cfz
    co
    #
    cun
    #
    @77
    c1
    @8
    wcel
    #
    @8
    @81
    wceq
    @82
    c1
    c3
    cle
    wbr
    #
    1le3
    c1
    cc0
    cuz
    cfv
    wcel
    c3
    cz
    wcel
    @82
    @83
    wb
    1eluzge0
    3z
    c1
    cc0
    c3
    elfz5
    mp2an
    mpbir
    c1
    cc0
    c3
    fzsplit
    ax-mp
    @78
    @20
    @80
    @22
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    cc0
    @84
    cpr
    #
    @78
    @20
    cc0
    cz
    wcel
    @85
    @86
    wceq
    0z
    cc0
    fzpr
    ax-mp
    c1
    @84
    cc0
    cfz
    1e0p1
    oveq2i
    c1
    @84
    cc0
    1e0p1
    preq2i
    3eqtr4i
    c2
    c2
    c1
    caddc
    co
    #
    cfz
    co
    #
    c2
    @87
    cpr
    #
    @80
    @22
    c2
    cz
    wcel
    @88
    @89
    wceq
    2z
    c2
    fzpr
    ax-mp
    @79
    c2
    c3
    @87
    cfz
    1p1e2
    df-3
    oveq12i
    c3
    @87
    c2
    df-3
    preq2i
    3eqtr4i
    uneq12i
    eqtri
    raleqi
    @7
    vk
    @20
    @22
    ralunb
    bitri
    @11
    @12
    @14
    @15
    an4
    3bitr4g
    anbi2d
    @1
    @13
    @16
    3anass
    syl6bbr
    bitrd
end
