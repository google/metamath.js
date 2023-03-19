include "cc0.mm"
include "c2.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cdiv.mm"
include "cmul.mm"
include "csin.mm"
include "cfv.mm"
include "clt.mm"
include "ccos.mm"
include "cr.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "2re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "rehalfcl.mm"
include "3ad2ant1.mm"
include "sylbi.mm"
include "resincl.mm"
include "recoscl.mm"
include "remulcld.mm"
include "syl.mm"
include "c1.mm"
include "wa.mm"
include "2pos.mm"
include "divgt0.mm"
include "mpanr12.mm"
include "3adant3.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "mp3an23.mm"
include "biimpa.mm"
include "2div2e1.mm"
include "syl6breq.mm"
include "3adant2.mm"
include "3jca.mm"
include "1re.mm"
include "3imtr4i.mm"
include "sin01gt0.mm"
include "cos01gt0.mm"
include "wi.mm"
include "axmulgt0.mm"
include "syl2anc.mm"
include "mp2and.mm"
include "mpan.mm"
include "mpani.mm"
include "sylc.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "sin2t.mm"
include "breqtrrd.mm"
include "simp1bi.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2.mm"
include "fveq2d.mm"
include "breqtrd.mm"

theorem sin02gt0
  let cA: class A


  assert |- ( A e. ( 0 (,] 2 ) -> 0 < ( sin ` A ) )

  proof
    cA
    cc0
    c2
    cioc
    co
    wcel
    #
    cc0
    c2
    cA
    c2
    cdiv
    co
    #
    cmul
    co
    #
    csin
    cfv
    #
    cA
    csin
    cfv
    clt
    @0
    cc0
    c2
    @1
    csin
    cfv
    #
    @1
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @3
    clt
    @0
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    cc0
    @7
    clt
    wbr
    #
    @0
    @1
    cr
    wcel
    #
    @8
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
    c2
    cle
    wbr
    #
    w3a
    #
    @11
    cc0
    cxr
    wcel
    #
    c2
    cr
    wcel
    #
    @0
    @15
    wb
    0xr
    2re
    cc0
    c2
    cA
    elioc2
    mp2an
    #
    @12
    @13
    @11
    @14
    cA
    rehalfcl
    3ad2ant1
    #
    sylbi
    #
    @11
    @4
    @5
    @1
    resincl
    #
    @1
    recoscl
    #
    remulcld
    syl
    @0
    cc0
    @4
    clt
    wbr
    #
    cc0
    @5
    clt
    wbr
    #
    @9
    @0
    @1
    cc0
    c1
    cioc
    co
    wcel
    #
    @23
    @15
    @11
    cc0
    @1
    clt
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    w3a
    #
    @0
    @25
    @15
    @11
    @26
    @27
    @19
    @12
    @13
    @26
    @14
    @12
    @13
    wa
    @17
    cc0
    c2
    clt
    wbr
    #
    @26
    2re
    2pos
    cA
    c2
    divgt0
    mpanr12
    3adant3
    @12
    @14
    @27
    @13
    @12
    @14
    wa
    @1
    c2
    c2
    cdiv
    co
    #
    c1
    cle
    @12
    @14
    @1
    @30
    cle
    wbr
    #
    @12
    @17
    @17
    @29
    wa
    @14
    @31
    wb
    2re
    @17
    @29
    2re
    2pos
    pm3.2i
    cA
    c2
    c2
    lediv1
    mp3an23
    biimpa
    2div2e1
    syl6breq
    3adant2
    3jca
    @18
    @16
    c1
    cr
    wcel
    @25
    @28
    wb
    0xr
    1re
    cc0
    c1
    @1
    elioc2
    mp2an
    3imtr4i
    #
    @1
    sin01gt0
    syl
    @0
    @25
    @24
    @32
    @1
    cos01gt0
    syl
    @0
    @11
    @23
    @24
    wa
    @9
    wi
    #
    @20
    @11
    @4
    cr
    wcel
    @5
    cr
    wcel
    @33
    @21
    @22
    @4
    @5
    axmulgt0
    syl2anc
    syl
    mp2and
    @8
    @29
    @9
    @10
    2pos
    @17
    @8
    @29
    @9
    wa
    @10
    wi
    2re
    c2
    @6
    axmulgt0
    mpan
    mpani
    sylc
    @0
    @1
    cc
    wcel
    @3
    @7
    wceq
    @0
    @1
    @20
    recnd
    @1
    sin2t
    syl
    breqtrrd
    @0
    @2
    cA
    csin
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    wceq
    #
    @0
    cA
    @0
    @12
    @13
    @14
    @18
    simp1bi
    recnd
    @34
    c2
    cc
    wcel
    c2
    cc0
    wne
    @35
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    syl
    fveq2d
    breqtrd
end
