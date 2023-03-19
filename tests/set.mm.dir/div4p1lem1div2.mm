include "cr.mm"
include "wcel.mm"
include "c6.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "c2.mm"
include "cmul.mm"
include "6re.mm"
include "a1i.mm"
include "id.mm"
include "leadd2d.mm"
include "biimpa.mm"
include "wceq.mm"
include "recn.mm"
include "times2d.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "wb.mm"
include "cc.mm"
include "4cn.mm"
include "2cn.mm"
include "addassd.mm"
include "4p2e6.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "mpbird.mm"
include "cc0.mm"
include "clt.mm"
include "4re.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "peano2re.mm"
include "syl.mm"
include "peano2rem.mm"
include "rehalfcld.mm"
include "4pos.mm"
include "pm3.2i.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "recnd.mm"
include "1cnd.mm"
include "divcan1d.mm"
include "mulid2i.mm"
include "oveq12d.mm"
include "joinlmuladdmuld.mm"
include "2t2e4.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "w3a.mm"
include "mulass.mm"
include "eqcomd.mm"
include "2ne0.mm"
include "oveq1d.mm"
include "subdird.mm"
include "3eqtrd.mm"
include "breq12d.mm"
include "readdcld.mm"
include "2re.mm"
include "remulcld.mm"
include "leaddsub.mm"
include "bicomd.mm"
include "3bitrd.mm"

theorem div4p1lem1div2
  let cN: class N


  assert |- ( ( N e. RR /\ 6 <_ N ) -> ( ( N / 4 ) + 1 ) <_ ( ( N - 1 ) / 2 ) )

  proof
    cN
    cr
    wcel
    #
    c6
    cN
    cle
    wbr
    #
    wa
    #
    cN
    c4
    cdiv
    co
    #
    c1
    caddc
    co
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cN
    c4
    caddc
    co
    #
    c2
    caddc
    co
    #
    cN
    c2
    cmul
    co
    #
    cle
    wbr
    #
    @2
    @11
    cN
    c6
    caddc
    co
    #
    @10
    cle
    wbr
    #
    @2
    @12
    cN
    cN
    caddc
    co
    #
    @10
    cle
    @0
    @1
    @12
    @14
    cle
    wbr
    @0
    c6
    cN
    cN
    c6
    cr
    wcel
    @0
    6re
    a1i
    @0
    id
    #
    @15
    leadd2d
    biimpa
    @0
    @10
    @14
    wceq
    @1
    @0
    cN
    cN
    recn
    #
    times2d
    adantr
    breqtrrd
    @0
    @11
    @13
    wb
    @1
    @0
    @9
    @12
    @10
    cle
    @0
    @9
    cN
    c4
    c2
    caddc
    co
    #
    caddc
    co
    @12
    @0
    cN
    c4
    c2
    @16
    c4
    cc
    wcel
    @0
    4cn
    a1i
    #
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    #
    addassd
    @17
    c6
    cN
    caddc
    4p2e6
    oveq2i
    syl6eq
    breq1d
    adantr
    mpbird
    @0
    @7
    @11
    wb
    @1
    @0
    @7
    @4
    c4
    cmul
    co
    #
    @6
    c4
    cmul
    co
    #
    cle
    wbr
    #
    @8
    @10
    c2
    cmin
    co
    #
    cle
    wbr
    #
    @11
    @0
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    c4
    cr
    wcel
    #
    cc0
    c4
    clt
    wbr
    #
    wa
    #
    @7
    @23
    wb
    @0
    @3
    cr
    wcel
    @26
    @0
    cN
    c4
    @15
    @27
    @0
    4re
    a1i
    #
    c4
    cc0
    wne
    @0
    4ne0
    a1i
    #
    redivcld
    #
    @3
    peano2re
    syl
    @0
    @5
    cN
    peano2rem
    #
    rehalfcld
    #
    @29
    @0
    @27
    @28
    4re
    4pos
    pm3.2i
    a1i
    @4
    @6
    c4
    lemul1
    syl3anc
    @0
    @21
    @8
    @22
    @24
    cle
    @0
    @3
    c4
    c1
    @8
    @0
    @3
    @32
    recnd
    @18
    @0
    1cnd
    #
    @0
    @3
    c4
    cmul
    co
    cN
    c1
    c4
    cmul
    co
    #
    c4
    caddc
    @0
    cN
    c4
    @16
    @18
    @31
    divcan1d
    @36
    c4
    wceq
    @0
    c4
    4cn
    mulid2i
    a1i
    oveq12d
    joinlmuladdmuld
    @0
    @22
    @6
    c2
    c2
    cmul
    co
    #
    cmul
    co
    #
    @6
    c2
    cmul
    co
    #
    c2
    cmul
    co
    #
    @24
    @0
    c4
    @37
    @6
    cmul
    c4
    @37
    wceq
    @0
    @37
    c4
    2t2e4
    eqcomi
    a1i
    oveq2d
    @0
    @6
    cc
    wcel
    #
    @19
    @19
    @38
    @40
    wceq
    @0
    @6
    @34
    recnd
    @20
    @20
    @41
    @19
    @19
    w3a
    @40
    @38
    @6
    c2
    c2
    mulass
    eqcomd
    syl3anc
    @0
    @40
    @5
    c2
    cmul
    co
    @10
    c1
    c2
    cmul
    co
    #
    cmin
    co
    @24
    @0
    @39
    @5
    c2
    cmul
    @0
    @5
    c2
    @0
    @5
    @33
    recnd
    @20
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan1d
    oveq1d
    @0
    cN
    c1
    c2
    @16
    @35
    @20
    subdird
    @0
    @42
    c2
    @10
    cmin
    @42
    c2
    wceq
    @0
    c2
    2cn
    mulid2i
    a1i
    oveq2d
    3eqtrd
    3eqtrd
    breq12d
    @0
    @8
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @25
    @11
    wb
    @0
    cN
    c4
    @15
    @30
    readdcld
    @44
    @0
    2re
    a1i
    #
    @0
    cN
    c2
    @15
    @46
    remulcld
    @43
    @44
    @45
    w3a
    @11
    @25
    @8
    c2
    @10
    leaddsub
    bicomd
    syl3anc
    3bitrd
    adantr
    mpbird
end
