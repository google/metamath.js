include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cva.mm"
include "cmul.mm"
include "cle.mm"
include "wral.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "cmv.mm"
include "wi.mm"
include "cr.mm"
include "wrex.mm"
include "wcel.mm"
include "cdiv.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "adantrr.mm"
include "recgt0.mm"
include "cneg.mm"
include "csm.mm"
include "1red.mm"
include "1re.mm"
include "chil.mm"
include "cc.mm"
include "neg1cn.mm"
include "sheli.mm"
include "hvmulcl.mm"
include "sylancr.mm"
include "normcl.mm"
include "syl.mm"
include "adantl.mm"
include "readdcl.mm"
include "adantr.mm"
include "hvsubcl.mm"
include "syl2an.mm"
include "remulcl.mm"
include "sylan2.mm"
include "anassrs.mm"
include "normge0.mm"
include "wb.mm"
include "addge01.mm"
include "mpan.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "csh.mm"
include "shmulcl.mm"
include "mp3an12.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "imp.mm"
include "ad2ant2lr.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "ad2antll.mm"
include "hvsubval.mm"
include "adantll.mm"
include "3brtr4d.mm"
include "letrd.mm"
include "ex.mm"
include "adantllr.mm"
include "simplll.mm"
include "simpllr.mm"
include "lediv1.mm"
include "mp3an1.mm"
include "syl12anc.mm"
include "sylibd.mm"
include "recnd.mm"
include "recn.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "divcan3d.mm"
include "breqtrd.mm"
include "exp43.mm"
include "com23.mm"
include "ralrimdv.mm"
include "ralimdva.mm"
include "impr.mm"
include "jca32.mm"
include "breq2.mm"
include "breq1.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl6.mm"
include "rexlimiv.mm"

theorem cdj1i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  assume cdj1.1: |- A e. SH
  assume cdj1.2: |- B e. SH

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint v x
  disjoint B x
  disjoint v y
  disjoint B y
  disjoint v z
  disjoint B z
  disjoint v w
  disjoint B w
  disjoint B v
  assert |- ( E. w e. RR ( 0 < w /\ A. y e. A A. v e. B ( ( normh ` y ) + ( normh ` v ) ) <_ ( w x. ( normh ` ( y +h v ) ) ) ) -> E. x e. RR ( 0 < x /\ A. y e. A A. z e. B ( ( normh ` y ) = 1 -> x <_ ( normh ` ( y -h z ) ) ) ) )

  proof
    cc0
    vw
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    cno
    cfv
    #
    vv
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @0
    @2
    @4
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vv
    cB
    wral
    #
    vy
    cA
    wral
    #
    wa
    #
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    @3
    c1
    wceq
    #
    @14
    @2
    vz
    cv
    #
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cB
    wral
    vy
    cA
    wral
    #
    wa
    #
    vx
    cr
    wrex
    #
    vw
    cr
    @0
    cr
    wcel
    #
    @13
    c1
    @0
    cdiv
    co
    #
    cr
    wcel
    #
    cc0
    @26
    clt
    wbr
    #
    @16
    @26
    @19
    cle
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    vy
    cA
    wral
    #
    wa
    #
    wa
    #
    @24
    @25
    @13
    @34
    @25
    @13
    wa
    @27
    @28
    @32
    @25
    @1
    @27
    @12
    @25
    @1
    @0
    cc0
    wne
    #
    @27
    @0
    gt0ne0
    #
    @0
    rereccl
    syldan
    adantrr
    @25
    @1
    @28
    @12
    @0
    recgt0
    adantrr
    @25
    @1
    @12
    @32
    @25
    @1
    wa
    #
    @11
    @31
    vy
    cA
    @37
    @2
    cA
    wcel
    #
    wa
    #
    @11
    @30
    vz
    cB
    @39
    @17
    cB
    wcel
    #
    @11
    @30
    @39
    @40
    @11
    @16
    @29
    @39
    @40
    wa
    #
    @11
    @16
    wa
    #
    wa
    @26
    @0
    @19
    cmul
    co
    #
    @0
    cdiv
    co
    #
    @19
    cle
    @41
    @42
    @26
    @44
    cle
    wbr
    #
    @41
    @42
    c1
    @43
    cle
    wbr
    #
    @45
    @25
    @38
    @40
    @42
    @46
    wi
    @1
    @25
    @38
    wa
    #
    @40
    wa
    #
    @42
    @46
    @48
    @42
    wa
    #
    c1
    c1
    c1
    cneg
    #
    @17
    csm
    co
    #
    cno
    cfv
    #
    caddc
    co
    #
    @43
    @49
    1red
    @48
    @53
    cr
    wcel
    #
    @42
    @48
    c1
    cr
    wcel
    #
    @52
    cr
    wcel
    #
    @54
    1re
    @40
    @56
    @47
    @40
    @51
    chil
    wcel
    #
    @56
    @40
    @50
    cc
    wcel
    #
    @17
    chil
    wcel
    #
    @57
    neg1cn
    @17
    cB
    cdj1.2
    sheli
    #
    @50
    @17
    hvmulcl
    sylancr
    #
    @51
    normcl
    syl
    #
    adantl
    c1
    @52
    readdcl
    sylancr
    adantr
    @48
    @43
    cr
    wcel
    #
    @42
    @25
    @38
    @40
    @63
    @38
    @40
    wa
    #
    @25
    @19
    cr
    wcel
    #
    @63
    @64
    @18
    chil
    wcel
    #
    @65
    @38
    @2
    chil
    wcel
    #
    @59
    @66
    @40
    @2
    cA
    cdj1.1
    sheli
    #
    @60
    @2
    @17
    hvsubcl
    syl2an
    #
    @18
    normcl
    #
    syl
    #
    @0
    @19
    remulcl
    #
    sylan2
    anassrs
    adantr
    @40
    c1
    @53
    cle
    wbr
    #
    @47
    @42
    @40
    @56
    cc0
    @52
    cle
    wbr
    #
    @73
    @62
    @40
    @57
    @74
    @61
    @51
    normge0
    syl
    @56
    @74
    @73
    @55
    @56
    @74
    @73
    wb
    1re
    c1
    @52
    addge01
    mpan
    biimpa
    syl2anc
    ad2antlr
    @49
    @3
    @52
    caddc
    co
    #
    @0
    @2
    @51
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    @53
    @43
    cle
    @40
    @11
    @75
    @78
    cle
    wbr
    #
    @47
    @16
    @40
    @11
    @79
    @40
    @51
    cB
    wcel
    #
    @11
    @79
    wi
    cB
    csh
    wcel
    @58
    @40
    @80
    cdj1.2
    neg1cn
    @50
    @17
    cB
    shmulcl
    mp3an12
    @10
    @79
    vv
    @51
    cB
    @4
    @51
    wceq
    #
    @6
    @75
    @9
    @78
    cle
    @81
    @5
    @52
    @3
    caddc
    @4
    @51
    cno
    fveq2
    oveq2d
    @81
    @8
    @77
    @0
    cmul
    @81
    @7
    @76
    cno
    @4
    @51
    @2
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    rspcv
    syl
    imp
    ad2ant2lr
    @16
    @53
    @75
    wceq
    #
    @48
    @11
    @82
    c1
    @3
    c1
    @3
    @52
    caddc
    oveq1
    eqcoms
    ad2antll
    @48
    @43
    @78
    wceq
    #
    @42
    @38
    @40
    @83
    @25
    @64
    @19
    @77
    @0
    cmul
    @64
    @18
    @76
    cno
    @38
    @67
    @59
    @18
    @76
    wceq
    @40
    @68
    @60
    @2
    @17
    hvsubval
    syl2an
    fveq2d
    oveq2d
    adantll
    adantr
    3brtr4d
    letrd
    ex
    adantllr
    @41
    @63
    @25
    @1
    @46
    @45
    wb
    #
    @41
    @25
    @65
    @63
    @25
    @1
    @38
    @40
    simplll
    #
    @41
    @66
    @65
    @38
    @40
    @66
    @37
    @69
    adantll
    @70
    syl
    @72
    syl2anc
    @85
    @25
    @1
    @38
    @40
    simpllr
    @55
    @63
    @37
    @84
    1re
    c1
    @43
    @0
    lediv1
    mp3an1
    syl12anc
    sylibd
    imp
    @41
    @44
    @19
    wceq
    @42
    @41
    @19
    @0
    @38
    @40
    @19
    cc
    wcel
    @37
    @64
    @19
    @71
    recnd
    adantll
    @25
    @0
    cc
    wcel
    @1
    @38
    @40
    @0
    recn
    ad3antrrr
    @37
    @35
    @38
    @40
    @36
    ad2antrr
    divcan3d
    adantr
    breqtrd
    exp43
    com23
    ralrimdv
    ralimdva
    impr
    jca32
    ex
    @23
    @33
    vx
    @26
    cr
    @14
    @26
    wceq
    #
    @15
    @28
    @22
    @32
    @14
    @26
    cc0
    clt
    breq2
    @86
    @21
    @30
    vy
    vz
    cA
    cB
    @86
    @20
    @29
    @16
    @14
    @26
    @19
    cle
    breq1
    imbi2d
    2ralbidv
    anbi12d
    rspcev
    syl6
    rexlimiv
end
