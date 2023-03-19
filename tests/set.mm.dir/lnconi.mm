include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cn.mm"
include "wa.mm"
include "clt.mm"
include "arch.mm"
include "adantr.mm"
include "wi.mm"
include "nnre.mm"
include "simplll.mm"
include "simpllr.mm"
include "normcl.mm"
include "adantl.mm"
include "cc0.mm"
include "normge0.mm"
include "ltle.mm"
include "imp.mm"
include "lemul1ad.mm"
include "simpll.mm"
include "remulcl.mm"
include "syl2an.mm"
include "simplr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "impancom.mm"
include "an32s.mm"
include "sylan2.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimiva.mm"
include "cmv.mm"
include "crp.mm"
include "cdiv.mm"
include "simprr.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "simprll.mm"
include "hvsubcl.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "eleq1d.mm"
include "vtoclga.mm"
include "syl.mm"
include "simprlr.mm"
include "rpred.mm"
include "lelttr.mm"
include "adantlr.mm"
include "mpand.mm"
include "wb.mm"
include "nnrp.mm"
include "rpregt0d.mm"
include "ltmuldiv2.mm"
include "breq1d.mm"
include "3imtr3d.mm"
include "anassrs.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralrimivva.mm"
include "sylibr.mm"
include "impbii.mm"

theorem lnconi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume lncon.1: |- ( T e. C -> S e. RR )
  assume lncon.2: |- ( ( T e. C /\ y e. ~H ) -> ( N ` ( T ` y ) ) <_ ( S x. ( normh ` y ) ) )
  assume lncon.3: |- ( T e. C <-> A. x e. ~H A. z e. RR+ E. y e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < y -> ( N ` ( ( T ` w ) M ( T ` x ) ) ) < z ) )
  assume lncon.4: |- ( y e. ~H -> ( N ` ( T ` y ) ) e. RR )
  assume lncon.5: |- ( ( w e. ~H /\ x e. ~H ) -> ( T ` ( w -h x ) ) = ( ( T ` w ) M ( T ` x ) ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint N w
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint M y
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint S x
  disjoint S y
  disjoint C y
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint M n
  disjoint T n
  assert |- ( T e. C <-> E. x e. RR A. y e. ~H ( N ` ( T ` y ) ) <_ ( x x. ( normh ` y ) ) )

  proof
    cT
    cC
    wcel
    #
    vy
    cv
    #
    cT
    cfv
    #
    cN
    cfv
    #
    vx
    cv
    #
    @1
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    vx
    cr
    wrex
    #
    @0
    cS
    cr
    wcel
    @3
    cS
    @5
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    @9
    lncon.1
    @0
    @11
    vy
    chil
    lncon.2
    ralrimiva
    @8
    @12
    vx
    cS
    cr
    @4
    cS
    wceq
    #
    @7
    @11
    vy
    chil
    @13
    @6
    @10
    @3
    cle
    @4
    cS
    @5
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    @9
    @3
    vn
    cv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    vn
    cn
    wrex
    #
    @0
    @8
    @18
    vx
    cr
    @4
    cr
    wcel
    #
    @8
    wa
    #
    @4
    @14
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @18
    @19
    @22
    @8
    @4
    vn
    arch
    adantr
    @20
    @21
    @17
    vn
    cn
    @14
    cn
    wcel
    #
    @20
    @14
    cr
    wcel
    #
    @21
    @17
    wi
    #
    @14
    nnre
    #
    @19
    @24
    @8
    @25
    @19
    @24
    wa
    #
    @21
    @8
    @17
    @27
    @21
    wa
    #
    @7
    @16
    vy
    chil
    @28
    @1
    chil
    wcel
    #
    wa
    #
    @7
    @6
    @15
    cle
    wbr
    #
    @16
    @30
    @4
    @14
    @5
    @19
    @24
    @21
    @29
    simplll
    @19
    @24
    @21
    @29
    simpllr
    @29
    @5
    cr
    wcel
    #
    @28
    @1
    normcl
    #
    adantl
    @29
    cc0
    @5
    cle
    wbr
    @28
    @1
    normge0
    adantl
    @28
    @4
    @14
    cle
    wbr
    #
    @29
    @27
    @21
    @34
    @4
    @14
    ltle
    imp
    adantr
    lemul1ad
    @30
    @3
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @7
    @31
    wa
    @16
    wi
    @29
    @35
    @28
    lncon.4
    adantl
    @28
    @19
    @32
    @36
    @29
    @19
    @24
    @21
    simpll
    @33
    @4
    @5
    remulcl
    syl2an
    @28
    @24
    @32
    @37
    @29
    @19
    @24
    @21
    simplr
    @33
    @14
    @5
    remulcl
    syl2an
    @3
    @6
    @15
    letr
    syl3anc
    mpan2d
    ralimdva
    impancom
    an32s
    sylan2
    reximdva
    mpd
    rexlimiva
    @18
    vw
    cv
    #
    @4
    cmv
    co
    #
    cno
    cfv
    #
    @1
    clt
    wbr
    #
    @38
    cT
    cfv
    @4
    cT
    cfv
    cM
    co
    #
    cN
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    #
    vy
    crp
    wrex
    #
    vz
    crp
    wral
    vx
    chil
    wral
    #
    @0
    @17
    @49
    vn
    cn
    @23
    @17
    wa
    #
    @48
    vx
    vz
    chil
    crp
    @50
    @4
    chil
    wcel
    #
    @44
    crp
    wcel
    #
    wa
    #
    wa
    #
    @44
    @14
    cdiv
    co
    #
    crp
    wcel
    @40
    @55
    clt
    wbr
    #
    @45
    wi
    #
    vw
    chil
    wral
    #
    @48
    @54
    @44
    @14
    @50
    @51
    @52
    simprr
    @54
    @14
    @23
    @17
    @53
    simpll
    nnrpd
    rpdivcld
    @54
    @57
    vw
    chil
    @50
    @53
    @38
    chil
    wcel
    #
    @57
    @50
    @53
    @59
    wa
    #
    wa
    #
    @14
    @40
    cmul
    co
    #
    @44
    clt
    wbr
    #
    @39
    cT
    cfv
    #
    cN
    cfv
    #
    @44
    clt
    wbr
    #
    @56
    @45
    @61
    @65
    @62
    cle
    wbr
    #
    @63
    @66
    @23
    @60
    @17
    @67
    @23
    @60
    wa
    #
    @39
    chil
    wcel
    #
    @17
    @67
    @68
    @59
    @51
    @69
    @23
    @53
    @59
    simprr
    #
    @23
    @51
    @52
    @59
    simprll
    #
    @38
    @4
    hvsubcl
    syl2anc
    #
    @16
    @67
    vy
    @39
    chil
    @1
    @39
    wceq
    #
    @3
    @65
    @15
    @62
    cle
    @73
    @2
    @64
    cN
    @1
    @39
    cT
    fveq2
    fveq2d
    #
    @73
    @5
    @40
    @14
    cmul
    @1
    @39
    cno
    fveq2
    oveq2d
    breq12d
    rspcva
    sylan
    an32s
    @23
    @60
    @67
    @63
    wa
    @66
    wi
    #
    @17
    @68
    @65
    cr
    wcel
    #
    @62
    cr
    wcel
    #
    @44
    cr
    wcel
    #
    @75
    @68
    @69
    @76
    @72
    @35
    @76
    vy
    @39
    chil
    @73
    @3
    @65
    cr
    @74
    eleq1d
    lncon.4
    vtoclga
    syl
    @68
    @24
    @40
    cr
    wcel
    #
    @77
    @23
    @24
    @60
    @26
    adantr
    @68
    @69
    @79
    @72
    @39
    normcl
    syl
    #
    @14
    @40
    remulcl
    syl2anc
    @68
    @44
    @23
    @51
    @52
    @59
    simprlr
    rpred
    #
    @65
    @62
    @44
    lelttr
    syl3anc
    adantlr
    mpand
    @23
    @60
    @63
    @56
    wb
    #
    @17
    @68
    @79
    @78
    @24
    cc0
    @14
    clt
    wbr
    wa
    #
    @82
    @80
    @81
    @23
    @83
    @60
    @23
    @14
    @14
    nnrp
    rpregt0d
    adantr
    @40
    @44
    @14
    ltmuldiv2
    syl3anc
    adantlr
    @61
    @65
    @43
    @44
    clt
    @61
    @64
    @42
    cN
    @23
    @60
    @64
    @42
    wceq
    #
    @17
    @68
    @59
    @51
    @84
    @70
    @71
    lncon.5
    syl2anc
    adantlr
    fveq2d
    breq1d
    3imtr3d
    anassrs
    ralrimiva
    @47
    @58
    vy
    @55
    crp
    @1
    @55
    wceq
    #
    @46
    @57
    vw
    chil
    @85
    @41
    @56
    @45
    @1
    @55
    @40
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    rexlimiva
    lncon.3
    sylibr
    syl
    impbii
end
