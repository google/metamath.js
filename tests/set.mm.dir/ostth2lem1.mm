include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cn.mm"
include "wrex.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "adantr.mm"
include "remulcl.mm"
include "sylancr.mm"
include "crp.mm"
include "simpr.mm"
include "wb.mm"
include "1re.mm"
include "difrp.mm"
include "mpbid.mm"
include "rerpdivcld.mm"
include "expnbnd.mm"
include "syl3anc.mm"
include "cn0.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "syl2an.mm"
include "rpred.mm"
include "nnre.mm"
include "adantl.mm"
include "remulcld.mm"
include "ad2antrr.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "syl.mm"
include "reexpcld.mm"
include "nnred.mm"
include "cz.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "0lt1.mm"
include "lttrd.mm"
include "elrpd.mm"
include "nnz.mm"
include "rpexpcl.mm"
include "caddc.mm"
include "peano2re.mm"
include "ltp1d.mm"
include "rpge0d.mm"
include "bernneq2.mm"
include "ltletrd.mm"
include "ltmul1dd.mm"
include "recnd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "expaddd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mul32d.mm"
include "2cnd.mm"
include "3brtr4d.mm"
include "nngt0.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "rpgt0d.mm"
include "ltmuldiv2.mm"
include "ltnsymd.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "lenlt.mm"
include "sylancl.mm"

theorem ostth2lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vk: setvar k
  assume ostth2lem1.1: |- ( ph -> A e. RR )
  assume ostth2lem1.2: |- ( ph -> B e. RR )
  assume ostth2lem1.3: |- ( ( ph /\ n e. NN ) -> ( A ^ n ) <_ ( n x. B ) )

  disjoint A n
  disjoint B n
  disjoint n ph
  disjoint k n
  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> A <_ 1 )

  proof
    wph
    cA
    c1
    cle
    wbr
    #
    c1
    cA
    clt
    wbr
    #
    wn
    #
    wph
    @1
    c2
    cB
    cmul
    co
    #
    cA
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    wph
    @1
    wa
    #
    @5
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @1
    @9
    @10
    @3
    @4
    @10
    c2
    cr
    wcel
    cB
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    2re
    wph
    @13
    @1
    ostth2lem1.2
    adantr
    c2
    cB
    remulcl
    sylancr
    #
    @10
    @1
    @4
    crp
    wcel
    #
    wph
    @1
    simpr
    #
    @10
    c1
    cr
    wcel
    #
    @12
    @1
    @16
    wb
    1re
    wph
    @12
    @1
    ostth2lem1.1
    adantr
    #
    c1
    cA
    difrp
    sylancr
    mpbid
    #
    rerpdivcld
    #
    @19
    @17
    @5
    cA
    vk
    expnbnd
    syl3anc
    @10
    @8
    vk
    cn
    @10
    @6
    cn
    wcel
    #
    wa
    #
    @7
    @5
    @10
    @12
    @6
    cn0
    wcel
    #
    @7
    cr
    wcel
    #
    @22
    @19
    @6
    nnnn0
    #
    cA
    @6
    reexpcl
    syl2an
    #
    @10
    @11
    @22
    @21
    adantr
    @23
    @4
    @7
    cmul
    co
    #
    @3
    clt
    wbr
    #
    @7
    @5
    clt
    wbr
    #
    @23
    @29
    @28
    @6
    cmul
    co
    #
    @3
    @6
    cmul
    co
    #
    clt
    wbr
    #
    @23
    @4
    @6
    cmul
    co
    #
    @7
    cmul
    co
    #
    c2
    @6
    cmul
    co
    #
    cB
    cmul
    co
    #
    @31
    @32
    clt
    @23
    @35
    cA
    @36
    cexp
    co
    #
    @37
    @23
    @34
    @7
    @23
    @4
    @6
    @10
    @4
    cr
    wcel
    #
    @22
    @10
    @4
    @20
    rpred
    adantr
    #
    @22
    @6
    cr
    wcel
    #
    @10
    @6
    nnre
    adantl
    #
    remulcld
    #
    @27
    remulcld
    @23
    cA
    @36
    wph
    @12
    @1
    @22
    ostth2lem1.1
    ad2antrr
    #
    @23
    @36
    cn
    wcel
    #
    @36
    cn0
    wcel
    @23
    c2
    cn
    wcel
    @22
    @45
    2nn
    @10
    @22
    simpr
    c2
    @6
    nnmulcl
    sylancr
    #
    @36
    nnnn0
    syl
    reexpcld
    @23
    @36
    cB
    @23
    @36
    @46
    nnred
    wph
    @13
    @1
    @22
    ostth2lem1.2
    ad2antrr
    #
    remulcld
    @23
    @35
    @7
    @7
    cmul
    co
    #
    @38
    clt
    @23
    @34
    @7
    @7
    @43
    @27
    @10
    cA
    crp
    wcel
    #
    @6
    cz
    wcel
    @7
    crp
    wcel
    @22
    @10
    cA
    @19
    @10
    cc0
    c1
    cA
    @10
    0red
    @18
    @10
    1re
    a1i
    @19
    cc0
    c1
    clt
    wbr
    @10
    0lt1
    a1i
    @17
    lttrd
    elrpd
    #
    @6
    nnz
    cA
    @6
    rpexpcl
    syl2an
    @23
    @34
    @34
    c1
    caddc
    co
    #
    @7
    @43
    @23
    @34
    cr
    wcel
    @51
    cr
    wcel
    @43
    @34
    peano2re
    syl
    @27
    @23
    @34
    @43
    ltp1d
    @23
    @12
    @24
    cc0
    cA
    cle
    wbr
    @51
    @7
    cle
    wbr
    @44
    @22
    @24
    @10
    @26
    adantl
    #
    @23
    cA
    @10
    @49
    @22
    @50
    adantr
    rpge0d
    cA
    @6
    bernneq2
    syl3anc
    ltletrd
    ltmul1dd
    @23
    @38
    cA
    @6
    @6
    caddc
    co
    #
    cexp
    co
    @48
    @23
    @36
    @53
    cA
    cexp
    @23
    @6
    @23
    @6
    @42
    recnd
    #
    2timesd
    oveq2d
    @23
    cA
    @6
    @6
    @23
    cA
    @44
    recnd
    @52
    @52
    expaddd
    eqtrd
    breqtrrd
    @23
    @45
    cA
    vn
    cv
    #
    cexp
    co
    #
    @55
    cB
    cmul
    co
    #
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @38
    @37
    cle
    wbr
    #
    @46
    wph
    @59
    @1
    @22
    wph
    @58
    vn
    cn
    ostth2lem1.3
    ralrimiva
    ad2antrr
    @58
    @60
    vn
    @36
    cn
    @55
    @36
    wceq
    @56
    @38
    @57
    @37
    cle
    @55
    @36
    cA
    cexp
    oveq2
    @55
    @36
    cB
    cmul
    oveq1
    breq12d
    rspcv
    sylc
    ltletrd
    @23
    @4
    @7
    @6
    @23
    @4
    @40
    recnd
    @23
    @7
    @27
    recnd
    @54
    mul32d
    @23
    c2
    cB
    @6
    @23
    2cnd
    @23
    cB
    @47
    recnd
    @54
    mul32d
    3brtr4d
    @23
    @28
    cr
    wcel
    @14
    @41
    cc0
    @6
    clt
    wbr
    #
    @29
    @33
    wb
    @23
    @4
    @7
    @40
    @27
    remulcld
    @10
    @14
    @22
    @15
    adantr
    #
    @42
    @22
    @61
    @10
    @6
    nngt0
    adantl
    @28
    @3
    @6
    ltmul1
    syl112anc
    mpbird
    @23
    @25
    @14
    @39
    cc0
    @4
    clt
    wbr
    #
    @29
    @30
    wb
    @27
    @62
    @40
    @10
    @63
    @22
    @10
    @4
    @20
    rpgt0d
    adantr
    @7
    @3
    @4
    ltmuldiv2
    syl112anc
    mpbid
    ltnsymd
    nrexdv
    pm2.65da
    wph
    @12
    @18
    @0
    @2
    wb
    ostth2lem1.1
    1re
    cA
    c1
    lenlt
    sylancl
    mpbird
end
