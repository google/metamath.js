include "cc0.mm"
include "wne.mm"
include "wo.mm"
include "c1.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "cneg.mm"
include "recni.mm"
include "sqcli.mm"
include "ax-icn.mm"
include "mulcli.mm"
include "negsubi.mm"
include "sqmuli.mm"
include "i2.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "mulneg1i.mm"
include "3eqtri.mm"
include "negeqi.mm"
include "negnegi.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "subsqi.mm"
include "3eqtr3ri.mm"
include "wa.mm"
include "wn.mm"
include "neorian.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "sumsqeq0.mm"
include "mp2an.mm"
include "necon3bbii.mm"
include "bitri.mm"
include "addcli.mm"
include "subcli.mm"
include "divasszi.mm"
include "sylbi.mm"
include "cc.mm"
include "divid.mm"
include "mpan.mm"
include "3eqtr3a.mm"
include "divclzi.mm"
include "a1i.mm"
include "crne0.mm"
include "biimpi.mm"
include "divmul.mm"
include "mp3an1.mm"
include "syl12anc.mm"
include "mpbird.mm"

theorem crreczi
  let cA: class A
  let cB: class B
  assume crrecz.1: |- A e. RR
  assume crrecz.2: |- B e. RR


  assert |- ( ( A =/= 0 \/ B =/= 0 ) -> ( 1 / ( A + ( _i x. B ) ) ) = ( ( A - ( _i x. B ) ) / ( ( A ^ 2 ) + ( B ^ 2 ) ) ) )

  proof
    cA
    cc0
    wne
    cB
    cc0
    wne
    wo
    #
    c1
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cdiv
    co
    cA
    @1
    cmin
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    wceq
    #
    @2
    @7
    cmul
    co
    #
    c1
    wceq
    #
    @0
    @2
    @3
    cmul
    co
    #
    @6
    cdiv
    co
    #
    @6
    @6
    cdiv
    co
    #
    @9
    c1
    @11
    @6
    @6
    cdiv
    @4
    @1
    c2
    cexp
    co
    #
    cneg
    #
    caddc
    co
    @4
    @14
    cmin
    co
    @6
    @11
    @4
    @14
    cA
    cA
    crrecz.1
    recni
    #
    sqcli
    #
    @1
    ci
    cB
    ax-icn
    cB
    crrecz.2
    recni
    #
    mulcli
    #
    sqcli
    negsubi
    @15
    @5
    @4
    caddc
    @15
    c1
    @5
    cmul
    co
    #
    cneg
    #
    cneg
    @20
    @5
    @14
    @21
    @14
    ci
    c2
    cexp
    co
    #
    @5
    cmul
    co
    c1
    cneg
    #
    @5
    cmul
    co
    @21
    ci
    cB
    ax-icn
    @18
    sqmuli
    @22
    @23
    @5
    cmul
    i2
    oveq1i
    c1
    @5
    ax-1cn
    cB
    @18
    sqcli
    #
    mulneg1i
    3eqtri
    negeqi
    @20
    c1
    @5
    ax-1cn
    @24
    mulcli
    negnegi
    @5
    @24
    mulid2i
    3eqtri
    oveq2i
    cA
    @1
    @16
    @19
    subsqi
    3eqtr3ri
    oveq1i
    @0
    @6
    cc0
    wne
    #
    @12
    @9
    wceq
    @0
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    #
    wn
    @25
    cA
    cc0
    cB
    cc0
    neorian
    @26
    @6
    cc0
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @26
    @6
    cc0
    wceq
    wb
    crrecz.1
    crrecz.2
    cA
    cB
    sumsqeq0
    mp2an
    necon3bbii
    bitri
    #
    @2
    @3
    @6
    cA
    @1
    @16
    @19
    addcli
    #
    cA
    @1
    @16
    @19
    subcli
    #
    @4
    @5
    @17
    @24
    addcli
    #
    divasszi
    sylbi
    @0
    @25
    @13
    c1
    wceq
    #
    @29
    @6
    cc
    wcel
    @25
    @33
    @32
    @6
    divid
    mpan
    sylbi
    3eqtr3a
    @0
    @7
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    @8
    @10
    wb
    #
    @0
    @25
    @34
    @29
    @3
    @6
    @31
    @32
    divclzi
    sylbi
    @35
    @0
    @30
    a1i
    @0
    @36
    @27
    @28
    @0
    @36
    wb
    crrecz.1
    crrecz.2
    cA
    cB
    crne0
    mp2an
    biimpi
    c1
    cc
    wcel
    @34
    @35
    @36
    wa
    @37
    ax-1cn
    c1
    @7
    @2
    divmul
    mp3an1
    syl12anc
    mpbird
end
