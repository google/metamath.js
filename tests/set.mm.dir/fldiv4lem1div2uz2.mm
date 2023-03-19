include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "cz.mm"
include "cr.mm"
include "eluzelz.mm"
include "zre.mm"
include "id.mm"
include "4re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "syl.mm"
include "flle.mm"
include "3syl.mm"
include "1red.mm"
include "eluzelre.mm"
include "rehalfcl.mm"
include "crp.mm"
include "2rp.mm"
include "eluzle.mm"
include "divge1.mm"
include "syl3anc.mm"
include "cc.mm"
include "wceq.mm"
include "eluzelcn.mm"
include "subhalfhalf.mm"
include "breqtrrd.mm"
include "lesubd.mm"
include "cmul.mm"
include "2t2e4.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "wa.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "peano2rem.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "3jca.mm"
include "lediv1.mm"
include "bitr4d.mm"
include "mpbird.mm"
include "wi.mm"
include "flcld.mm"
include "zred.mm"
include "rehalfcld.mm"
include "letr.mm"
include "mp2and.mm"

theorem fldiv4lem1div2uz2
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( |_ ` ( N / 4 ) ) <_ ( ( N - 1 ) / 2 ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    @1
    cle
    wbr
    #
    @1
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
    @2
    @5
    cle
    wbr
    #
    @0
    cN
    cz
    wcel
    #
    @1
    cr
    wcel
    #
    @3
    c2
    cN
    eluzelz
    #
    @8
    cN
    cr
    wcel
    #
    @9
    cN
    zre
    #
    @11
    cN
    c4
    @11
    id
    c4
    cr
    wcel
    @11
    4re
    a1i
    c4
    cc0
    wne
    @11
    4ne0
    a1i
    redivcld
    #
    syl
    @1
    flle
    3syl
    @0
    @6
    cN
    c2
    cdiv
    co
    #
    @4
    cle
    wbr
    #
    @0
    c1
    cN
    @14
    @0
    1red
    c2
    cN
    eluzelre
    #
    @0
    @8
    @11
    @14
    cr
    wcel
    #
    @10
    @12
    cN
    rehalfcl
    #
    3syl
    @0
    c1
    @14
    cN
    @14
    cmin
    co
    #
    cle
    @0
    c2
    crp
    wcel
    #
    @11
    c2
    cN
    cle
    wbr
    c1
    @14
    cle
    wbr
    @20
    @0
    2rp
    a1i
    @16
    c2
    cN
    eluzle
    c2
    cN
    divge1
    syl3anc
    @0
    cN
    cc
    wcel
    #
    @19
    @14
    wceq
    c2
    cN
    eluzelcn
    #
    cN
    subhalfhalf
    syl
    breqtrrd
    lesubd
    @0
    @6
    @14
    c2
    cdiv
    co
    #
    @5
    cle
    wbr
    #
    @15
    @0
    @1
    @23
    @5
    cle
    @0
    @1
    cN
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @23
    @0
    c4
    @25
    cN
    cdiv
    c4
    @25
    wceq
    @0
    @25
    c4
    2t2e4
    eqcomi
    a1i
    oveq2d
    @0
    @21
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @27
    @23
    @26
    wceq
    @22
    @27
    @0
    2cnne0
    a1i
    #
    @28
    cN
    c2
    c2
    divdiv1
    syl3anc
    eqtr4d
    breq1d
    @0
    @17
    @4
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    w3a
    #
    @15
    @24
    wb
    @0
    @8
    @11
    @33
    @10
    @12
    @11
    @17
    @29
    @32
    @18
    cN
    peano2rem
    #
    @32
    @11
    @30
    @31
    2re
    2pos
    pm3.2i
    a1i
    3jca
    3syl
    @14
    @4
    c2
    lediv1
    syl
    bitr4d
    mpbird
    @0
    @2
    cr
    wcel
    #
    @9
    @5
    cr
    wcel
    #
    w3a
    #
    @3
    @6
    wa
    @7
    wi
    @0
    @8
    @11
    @37
    @10
    @12
    @11
    @35
    @9
    @36
    @11
    @2
    @11
    @1
    @13
    flcld
    zred
    @13
    @11
    @4
    @34
    rehalfcld
    3jca
    3syl
    @2
    @1
    @5
    letr
    syl
    mp2and
end
