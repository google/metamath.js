include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "c3.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "ccos.mm"
include "cfv.mm"
include "cle.mm"
include "cc.mm"
include "wceq.mm"
include "cr.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "resqcld.mm"
include "recnd.mm"
include "wne.mm"
include "wa.mm"
include "2cn.mm"
include "3cn.mm"
include "3ne0.mm"
include "pm3.2i.mm"
include "div12.mm"
include "mp3an13.mm"
include "syl.mm"
include "cz.mm"
include "2z.mm"
include "expgt0.mm"
include "mp3an2.mm"
include "3adant3.mm"
include "sylbi.mm"
include "2lt3.mm"
include "2re.mm"
include "3re.mm"
include "3pos.mm"
include "ltdiv1ii.mm"
include "mpbi.mm"
include "dividi.mm"
include "breqtri.mm"
include "redivcli.mm"
include "ltmul2.mm"
include "mp3an12.mm"
include "mpbii.mm"
include "syl2anc.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "imdistani.mm"
include "le2sq2.mm"
include "mpanr1.mm"
include "stoic3.mm"
include "sq1.mm"
include "syl6breq.mm"
include "redivcl.mm"
include "mp3an23.mm"
include "remulcl.mm"
include "sylancr.mm"
include "ltletr.mm"
include "mp3an3.mm"
include "mp2and.mm"
include "posdif.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cos01bnd.mm"
include "simpld.mm"
include "resubcl.mm"
include "recoscld.mm"
include "lttr.mm"
include "mp3an1.mm"

theorem cos01gt0
  let cA: class A


  assert |- ( A e. ( 0 (,] 1 ) -> 0 < ( cos ` A ) )

  proof
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    cc0
    c1
    c2
    cA
    c2
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    @4
    cA
    ccos
    cfv
    #
    clt
    wbr
    #
    cc0
    @6
    clt
    wbr
    #
    @0
    @3
    c1
    clt
    wbr
    #
    @5
    @0
    @3
    @1
    clt
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    @9
    @0
    @3
    @1
    c2
    c3
    cdiv
    co
    #
    cmul
    co
    #
    @1
    clt
    @0
    @1
    cc
    wcel
    #
    @3
    @13
    wceq
    #
    @0
    @1
    @0
    cA
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    #
    @0
    @16
    @17
    @18
    w3a
    #
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    #
    simp1bi
    #
    resqcld
    #
    recnd
    #
    c2
    cc
    wcel
    @14
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    wa
    @15
    2cn
    @25
    @26
    3cn
    3ne0
    pm3.2i
    c2
    @1
    c3
    div12
    mp3an13
    syl
    @0
    @13
    @1
    c1
    cmul
    co
    #
    @1
    clt
    @0
    @1
    cr
    wcel
    #
    cc0
    @1
    clt
    wbr
    #
    @13
    @27
    clt
    wbr
    #
    @23
    @0
    @20
    @29
    @21
    @16
    @17
    @29
    @18
    @16
    c2
    cz
    wcel
    @17
    @29
    2z
    cA
    c2
    expgt0
    mp3an2
    3adant3
    sylbi
    @28
    @29
    wa
    #
    @12
    c1
    clt
    wbr
    #
    @30
    @12
    c3
    c3
    cdiv
    co
    #
    c1
    clt
    c2
    c3
    clt
    wbr
    @12
    @33
    clt
    wbr
    2lt3
    c2
    c3
    c3
    2re
    3re
    3re
    3pos
    ltdiv1ii
    mpbi
    c3
    3cn
    3ne0
    dividi
    breqtri
    @12
    cr
    wcel
    @19
    @31
    @32
    @30
    wb
    c2
    c3
    2re
    3re
    3ne0
    redivcli
    1re
    @12
    c1
    @1
    ltmul2
    mp3an12
    mpbii
    syl2anc
    @0
    @1
    @24
    mulid1d
    breqtrd
    eqbrtrd
    @0
    @1
    c1
    c2
    cexp
    co
    #
    c1
    cle
    @0
    @20
    @1
    @34
    cle
    wbr
    #
    @21
    @16
    @17
    @16
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    @18
    @35
    @16
    @17
    @36
    cc0
    cr
    wcel
    #
    @16
    @17
    @36
    wi
    0re
    cc0
    cA
    ltle
    mpan
    imdistani
    @37
    @19
    @18
    @35
    1re
    cA
    c1
    le2sq2
    mpanr1
    stoic3
    sylbi
    sq1
    syl6breq
    @0
    @3
    cr
    wcel
    #
    @28
    @10
    @11
    wa
    @9
    wi
    #
    @0
    c2
    cr
    wcel
    @2
    cr
    wcel
    #
    @39
    2re
    @0
    @28
    @41
    @23
    @28
    c3
    cr
    wcel
    @26
    @41
    3re
    3ne0
    @1
    c3
    redivcl
    mp3an23
    syl
    c2
    @2
    remulcl
    sylancr
    #
    @23
    @39
    @28
    @19
    @40
    1re
    @3
    @1
    c1
    ltletr
    mp3an3
    syl2anc
    mp2and
    @0
    @39
    @19
    @9
    @5
    wb
    @42
    1re
    @3
    c1
    posdif
    sylancl
    mpbid
    @0
    @7
    @6
    c1
    @2
    cmin
    co
    clt
    wbr
    cA
    cos01bnd
    simpld
    @0
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @5
    @7
    wa
    @8
    wi
    #
    @0
    @19
    @39
    @43
    1re
    @42
    c1
    @3
    resubcl
    sylancr
    @0
    cA
    @22
    recoscld
    @38
    @43
    @44
    @45
    0re
    cc0
    @4
    @6
    lttr
    mp3an1
    syl2anc
    mp2and
end
