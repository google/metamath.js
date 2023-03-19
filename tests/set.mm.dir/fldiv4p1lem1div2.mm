include "c3.mm"
include "wceq.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "c5.mm"
include "cuz.mm"
include "wcel.mm"
include "1le1.mm"
include "a1i.mm"
include "cc0.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "clt.mm"
include "3lt4.mm"
include "cn0.mm"
include "cn.mm"
include "wb.mm"
include "3nn0.mm"
include "4nn.mm"
include "divfl0.mm"
include "mp2an.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "3m1e2.mm"
include "2div2e1.mm"
include "3brtr4d.mm"
include "wo.mm"
include "uzp1.mm"
include "2re.mm"
include "leidi.mm"
include "df-5.mm"
include "oveq1i.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "4ne0.mm"
include "divdiri.mm"
include "dividi.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "cr.mm"
include "1re.mm"
include "0le1.mm"
include "4re.mm"
include "4pos.mm"
include "divge0.mm"
include "mp4an.mm"
include "1lt4.mm"
include "recgt1.mm"
include "cz.mm"
include "wa.mm"
include "1z.mm"
include "rereccli.mm"
include "flbi2.mm"
include "mpbir2an.mm"
include "1p1e2.mm"
include "mvrraddi.mm"
include "4d2e2.mm"
include "c6.mm"
include "w3a.mm"
include "eluz2.mm"
include "zre.mm"
include "id.mm"
include "wne.mm"
include "redivcld.mm"
include "flle.mm"
include "3syl.mm"
include "adantr.mm"
include "flcld.mm"
include "zred.mm"
include "3jca.mm"
include "syl.mm"
include "leadd1.mm"
include "mpbid.mm"
include "div4p1lem1div2.mm"
include "sylan.mm"
include "wi.mm"
include "peano2re.mm"
include "peano2rem.mm"
include "rehalfcld.mm"
include "letr.mm"
include "mp2and.mm"
include "3adant1.mm"
include "sylbi.mm"
include "5p1e6.mm"
include "eleq2s.mm"
include "jaoi.mm"

theorem fldiv4p1lem1div2
  let cN: class N


  assert |- ( ( N = 3 \/ N e. ( ZZ>= ` 5 ) ) -> ( ( |_ ` ( N / 4 ) ) + 1 ) <_ ( ( N - 1 ) / 2 ) )

  proof
    cN
    c3
    wceq
    #
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
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
    c5
    cuz
    cfv
    wcel
    #
    @0
    c1
    c1
    @3
    @5
    cle
    c1
    c1
    cle
    wbr
    @0
    1le1
    a1i
    @0
    @3
    cc0
    c1
    caddc
    co
    c1
    @0
    @2
    cc0
    c1
    caddc
    @0
    @2
    c3
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cc0
    @0
    @1
    @8
    cfl
    cN
    c3
    c4
    cdiv
    oveq1
    fveq2d
    c3
    c4
    clt
    wbr
    #
    @9
    cc0
    wceq
    #
    3lt4
    c3
    cn0
    wcel
    c4
    cn
    wcel
    @10
    @11
    wb
    3nn0
    4nn
    c3
    c4
    divfl0
    mp2an
    mpbi
    syl6eq
    oveq1d
    0p1e1
    syl6eq
    @0
    @5
    c2
    c2
    cdiv
    co
    c1
    @0
    @4
    c2
    c2
    cdiv
    @0
    @4
    c3
    c1
    cmin
    co
    c2
    cN
    c3
    c1
    cmin
    oveq1
    3m1e2
    syl6eq
    oveq1d
    2div2e1
    syl6eq
    3brtr4d
    @7
    cN
    c5
    wceq
    #
    cN
    c5
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wo
    @6
    c5
    cN
    uzp1
    @12
    @6
    @15
    @12
    c2
    c2
    @3
    @5
    cle
    c2
    c2
    cle
    wbr
    @12
    c2
    2re
    leidi
    a1i
    @12
    @3
    c1
    c1
    caddc
    co
    c2
    @12
    @2
    c1
    c1
    caddc
    @12
    @2
    c5
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    @12
    @1
    @16
    cfl
    cN
    c5
    c4
    cdiv
    oveq1
    fveq2d
    @17
    c1
    c1
    c4
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    c1
    @16
    @19
    cfl
    @16
    c4
    c1
    caddc
    co
    #
    c4
    cdiv
    co
    #
    @19
    c5
    @21
    c4
    cdiv
    df-5
    oveq1i
    @22
    c4
    c4
    cdiv
    co
    #
    @18
    caddc
    co
    @19
    c4
    c1
    c4
    4cn
    ax-1cn
    4cn
    4ne0
    divdiri
    @23
    c1
    @18
    caddc
    c4
    4cn
    4ne0
    dividi
    oveq1i
    eqtri
    eqtri
    fveq2i
    @20
    c1
    wceq
    #
    cc0
    @18
    cle
    wbr
    #
    @18
    c1
    clt
    wbr
    #
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    c4
    cr
    wcel
    #
    cc0
    c4
    clt
    wbr
    #
    @25
    1re
    0le1
    4re
    4pos
    c1
    c4
    divge0
    mp4an
    c1
    c4
    clt
    wbr
    #
    @26
    1lt4
    @28
    @29
    @30
    @26
    wb
    4re
    4pos
    c4
    recgt1
    mp2an
    mpbi
    c1
    cz
    wcel
    @18
    cr
    wcel
    @24
    @25
    @26
    wa
    wb
    1z
    c4
    4re
    4ne0
    rereccli
    @18
    c1
    flbi2
    mp2an
    mpbir2an
    eqtri
    syl6eq
    oveq1d
    1p1e2
    syl6eq
    @12
    @5
    c4
    c2
    cdiv
    co
    c2
    @12
    @4
    c4
    c2
    cdiv
    @12
    @4
    c5
    c1
    cmin
    co
    c4
    cN
    c5
    c1
    cmin
    oveq1
    c5
    c4
    c1
    4cn
    ax-1cn
    df-5
    mvrraddi
    syl6eq
    oveq1d
    4d2e2
    syl6eq
    3brtr4d
    @6
    cN
    c6
    cuz
    cfv
    #
    @14
    cN
    @31
    wcel
    c6
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c6
    cN
    cle
    wbr
    #
    w3a
    @6
    c6
    cN
    eluz2
    @33
    @34
    @6
    @32
    @33
    @34
    wa
    #
    @3
    @1
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @36
    @5
    cle
    wbr
    #
    @6
    @35
    @2
    @1
    cle
    wbr
    #
    @37
    @33
    @39
    @34
    @33
    cN
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @39
    cN
    zre
    #
    @40
    cN
    c4
    @40
    id
    @28
    @40
    4re
    a1i
    c4
    cc0
    wne
    @40
    4ne0
    a1i
    redivcld
    #
    @1
    flle
    3syl
    adantr
    @35
    @2
    cr
    wcel
    #
    @41
    @27
    w3a
    #
    @39
    @37
    wb
    @33
    @45
    @34
    @33
    @40
    @45
    @42
    @40
    @44
    @41
    @27
    @40
    @2
    @40
    @1
    @43
    flcld
    zred
    #
    @43
    @27
    @40
    1re
    a1i
    3jca
    syl
    adantr
    @2
    @1
    c1
    leadd1
    syl
    mpbid
    @33
    @40
    @34
    @38
    @42
    cN
    div4p1lem1div2
    sylan
    @35
    @3
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    w3a
    #
    @37
    @38
    wa
    @6
    wi
    @33
    @50
    @34
    @33
    @40
    @50
    @42
    @40
    @47
    @48
    @49
    @40
    @44
    @47
    @46
    @2
    peano2re
    syl
    @40
    @41
    @48
    @43
    @1
    peano2re
    syl
    @40
    @4
    cN
    peano2rem
    rehalfcld
    3jca
    syl
    adantr
    @3
    @36
    @5
    letr
    syl
    mp2and
    3adant1
    sylbi
    @13
    c6
    cuz
    5p1e6
    fveq2i
    eleq2s
    jaoi
    syl
    jaoi
end
