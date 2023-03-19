include "cr.mm"
include "wcel.mm"
include "c8.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "crp.mm"
include "2rp.mm"
include "c4.mm"
include "cn.mm"
include "cuz.mm"
include "4nn.mm"
include "cz.mm"
include "4z.mm"
include "a1i.mm"
include "cfl.mm"
include "rehalfcl.mm"
include "adantr.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "4t2e8.mm"
include "simpr.mm"
include "syl5eqbr.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "4re.mm"
include "simpl.mm"
include "2re.mm"
include "2pos.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "flge.mm"
include "sylancl.mm"
include "syl6breqr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eluznn.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpmulcl.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "0red.mm"
include "8re.mm"
include "8pos.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "remulcl.mm"
include "c1.mm"
include "caddc.mm"
include "zred.mm"
include "peano2re.mm"
include "syl.mm"
include "flltp1.mm"
include "oveq1i.mm"
include "1red.mm"
include "nnge1d.mm"
include "leadd2dd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "ceu.mm"
include "ere.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpri.mm"
include "3lt4.mm"
include "3re.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltled.mm"
include "lttrd.mm"
include "logdivlt.mm"
include "syl22anc.mm"
include "rphalflt.mm"
include "logltb.mm"
include "syl2anc.mm"
include "ltdiv1dd.mm"
include "rpne0d.mm"
include "wne.mm"
include "2ne0.mm"
include "divdiv2d.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "divassd.mm"
include "3eqtrd.mm"
include "breqtrd.mm"

theorem chebbnd1lem2
  let cM: class M
  let cN: class N
  assume chebbnd1lem2.1: |- M = ( |_ ` ( N / 2 ) )


  assert |- ( ( N e. RR /\ 8 <_ N ) -> ( ( log ` ( 2 x. M ) ) / ( 2 x. M ) ) < ( 2 x. ( ( log ` N ) / N ) ) )

  proof
    cN
    cr
    wcel
    #
    c8
    cN
    cle
    wbr
    #
    wa
    #
    c2
    cM
    cmul
    co
    #
    clog
    cfv
    #
    @3
    cdiv
    co
    #
    cN
    c2
    cdiv
    co
    #
    clog
    cfv
    #
    @6
    cdiv
    co
    #
    c2
    cN
    clog
    cfv
    #
    cN
    cdiv
    co
    #
    cmul
    co
    #
    @2
    @4
    @3
    @2
    @3
    @2
    c2
    crp
    wcel
    cM
    crp
    wcel
    @3
    crp
    wcel
    2rp
    @2
    cM
    @2
    c4
    cn
    wcel
    cM
    c4
    cuz
    cfv
    wcel
    #
    cM
    cn
    wcel
    4nn
    @2
    c4
    cz
    wcel
    #
    cM
    cz
    wcel
    c4
    cM
    cle
    wbr
    @12
    @13
    @2
    4z
    a1i
    @2
    cM
    @6
    cfl
    cfv
    #
    cz
    chebbnd1lem2.1
    @2
    @6
    @0
    @6
    cr
    wcel
    #
    @1
    cN
    rehalfcl
    adantr
    #
    flcld
    syl5eqel
    #
    @2
    c4
    @14
    cM
    cle
    @2
    c4
    @6
    cle
    wbr
    #
    c4
    @14
    cle
    wbr
    #
    @2
    c4
    c2
    cmul
    co
    #
    cN
    cle
    wbr
    #
    @18
    @2
    @20
    c8
    cN
    cle
    4t2e8
    @0
    @1
    simpr
    #
    syl5eqbr
    @2
    c4
    cr
    wcel
    #
    @0
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @21
    @18
    wb
    @23
    @2
    4re
    a1i
    #
    @0
    @1
    simpl
    #
    @24
    @2
    2re
    a1i
    #
    @25
    @2
    2pos
    a1i
    c4
    cN
    c2
    lemuldiv
    syl112anc
    mpbid
    #
    @2
    @15
    @13
    @18
    @19
    wb
    @16
    4z
    @6
    c4
    flge
    sylancl
    mpbid
    chebbnd1lem2.1
    syl6breqr
    c4
    cM
    eluz2
    syl3anbrc
    cM
    c4
    eluznn
    sylancr
    #
    nnrpd
    c2
    cM
    rpmulcl
    sylancr
    #
    relogcld
    @31
    rerpdivcld
    @2
    @7
    @6
    @2
    @6
    @2
    cN
    @2
    cN
    @27
    @2
    cc0
    c8
    cN
    @2
    0red
    c8
    cr
    wcel
    @2
    8re
    a1i
    @27
    cc0
    c8
    clt
    wbr
    @2
    8pos
    a1i
    @22
    ltletrd
    elrpd
    #
    rphalfcld
    #
    relogcld
    #
    @33
    rerpdivcld
    @2
    @24
    @10
    cr
    wcel
    @11
    cr
    wcel
    2re
    @2
    @9
    cN
    @2
    cN
    @32
    relogcld
    #
    @32
    rerpdivcld
    c2
    @10
    remulcl
    sylancr
    @2
    @6
    @3
    clt
    wbr
    #
    @5
    @8
    clt
    wbr
    #
    @2
    @6
    cM
    c1
    caddc
    co
    #
    @3
    @16
    @2
    cM
    cr
    wcel
    #
    @38
    cr
    wcel
    @2
    cM
    @17
    zred
    #
    cM
    peano2re
    syl
    @2
    @24
    @39
    @3
    cr
    wcel
    #
    2re
    @40
    c2
    cM
    remulcl
    sylancr
    #
    @2
    @6
    @14
    c1
    caddc
    co
    #
    @38
    clt
    @2
    @15
    @6
    @43
    clt
    wbr
    @16
    @6
    flltp1
    syl
    cM
    @14
    c1
    caddc
    chebbnd1lem2.1
    oveq1i
    syl6breqr
    @2
    @38
    cM
    cM
    caddc
    co
    @3
    cle
    @2
    c1
    cM
    cM
    @2
    1red
    @40
    @40
    @2
    cM
    @30
    nnge1d
    leadd2dd
    @2
    cM
    @2
    cM
    @40
    recnd
    2timesd
    breqtrrd
    ltletrd
    #
    @2
    @15
    ceu
    @6
    cle
    wbr
    @41
    ceu
    @3
    cle
    wbr
    @36
    @37
    wb
    @16
    @2
    ceu
    @6
    ceu
    cr
    wcel
    @2
    ere
    a1i
    #
    @16
    @2
    ceu
    c4
    @6
    @45
    @26
    @16
    ceu
    c4
    clt
    wbr
    #
    @2
    ceu
    c3
    clt
    wbr
    #
    c3
    c4
    clt
    wbr
    @46
    c2
    ceu
    clt
    wbr
    @47
    egt2lt3
    simpri
    3lt4
    ceu
    c3
    c4
    ere
    3re
    4re
    lttri
    mp2an
    a1i
    @29
    ltletrd
    #
    ltled
    @42
    @2
    ceu
    @3
    @45
    @42
    @2
    ceu
    @6
    @3
    @45
    @16
    @42
    @48
    @44
    lttrd
    ltled
    @6
    @3
    logdivlt
    syl22anc
    mpbid
    @2
    @8
    @9
    @6
    cdiv
    co
    #
    @11
    clt
    @2
    @7
    @9
    @6
    @34
    @35
    @33
    @2
    @6
    cN
    clt
    wbr
    #
    @7
    @9
    clt
    wbr
    #
    @2
    cN
    crp
    wcel
    #
    @50
    @32
    cN
    rphalflt
    syl
    @2
    @6
    crp
    wcel
    @52
    @50
    @51
    wb
    @33
    @32
    @6
    cN
    logltb
    syl2anc
    mpbid
    ltdiv1dd
    @2
    @49
    @9
    c2
    cmul
    co
    #
    cN
    cdiv
    co
    c2
    @9
    cmul
    co
    #
    cN
    cdiv
    co
    @11
    @2
    @9
    cN
    c2
    @2
    @9
    @35
    recnd
    #
    @2
    cN
    @27
    recnd
    #
    @2
    c2
    @28
    recnd
    #
    @2
    cN
    @32
    rpne0d
    #
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    divdiv2d
    @2
    @53
    @54
    cN
    cdiv
    @2
    @9
    c2
    @55
    @57
    mulcomd
    oveq1d
    @2
    c2
    @9
    cN
    @57
    @55
    @56
    @58
    divassd
    3eqtrd
    breqtrd
    lttrd
end
