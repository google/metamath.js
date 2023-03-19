include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ccos.mm"
include "cc0.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "lt0neg1.mm"
include "mtbi.mm"
include "cioc.mm"
include "cle.mm"
include "pire.mm"
include "rehalfcli.mm"
include "2re.mm"
include "pipos.mm"
include "2pos.mm"
include "divgt0ii.mm"
include "c4.mm"
include "4re.mm"
include "pigt2lt4.mm"
include "simpri.mm"
include "ltleii.mm"
include "cmul.mm"
include "wa.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an.mm"
include "2t2e4.mm"
include "breq2i.mm"
include "bitr2i.mm"
include "mpbi.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "sin02gt0.mm"
include "breq2.mm"
include "mpbii.mm"
include "mto.mm"
include "cexp.mm"
include "wo.mm"
include "caddc.mm"
include "sq1.mm"
include "resincl.mm"
include "gt0ne0ii.mm"
include "neii.mm"
include "2ne0.mm"
include "recni.mm"
include "2cn.mm"
include "divcan2i.mm"
include "fveq2i.mm"
include "cc.mm"
include "sin2t.mm"
include "eqtr3i.mm"
include "sinpi.mm"
include "sincl.mm"
include "coscl.mm"
include "mulcli.mm"
include "mul0ori.mm"
include "mtpor.mm"
include "oveq1i.mm"
include "sq0.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "sincossq.mm"
include "sqcli.mm"
include "addid1i.mm"
include "3eqtr2ri.mm"
include "ax-1cn.mm"
include "sqeqori.mm"
include "ori.mm"
include "mt3.mm"

theorem sinhalfpilem



  assert |- ( ( sin ` ( _pi / 2 ) ) = 1 /\ ( cos ` ( _pi / 2 ) ) = 0 )

  proof
    cpi
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    c1
    wceq
    #
    @0
    ccos
    cfv
    #
    cc0
    wceq
    #
    @2
    @1
    c1
    cneg
    #
    wceq
    #
    @6
    cc0
    @5
    clt
    wbr
    #
    c1
    cc0
    clt
    wbr
    #
    @7
    cc0
    c1
    clt
    wbr
    @8
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    ax-mp
    c1
    cr
    wcel
    @8
    @7
    wb
    1re
    c1
    lt0neg1
    ax-mp
    mtbi
    @6
    cc0
    @1
    clt
    wbr
    #
    @7
    @0
    cc0
    c2
    cioc
    co
    wcel
    #
    @9
    @10
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    @0
    c2
    cle
    wbr
    #
    cpi
    pire
    rehalfcli
    #
    cpi
    c2
    pire
    2re
    pipos
    2pos
    divgt0ii
    cpi
    c4
    cle
    wbr
    #
    @13
    cpi
    c4
    pire
    4re
    c2
    cpi
    clt
    wbr
    cpi
    c4
    clt
    wbr
    pigt2lt4
    simpri
    ltleii
    @13
    cpi
    c2
    c2
    cmul
    co
    #
    cle
    wbr
    #
    @15
    cpi
    cr
    wcel
    c2
    cr
    wcel
    #
    @18
    cc0
    c2
    clt
    wbr
    #
    wa
    @13
    @17
    wb
    pire
    2re
    @18
    @19
    2re
    2pos
    pm3.2i
    cpi
    c2
    c2
    ledivmul
    mp3an
    @16
    c4
    cpi
    cle
    2t2e4
    breq2i
    bitr2i
    mpbi
    cc0
    cxr
    wcel
    @18
    @10
    @11
    @12
    @13
    w3a
    wb
    0xr
    2re
    cc0
    c2
    @0
    elioc2
    mp2an
    mpbir3an
    @0
    sin02gt0
    ax-mp
    #
    @1
    @5
    cc0
    clt
    breq2
    mpbii
    mto
    @2
    @6
    @1
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    wceq
    @2
    @6
    wo
    @22
    c1
    @21
    cc0
    caddc
    co
    #
    @21
    sq1
    @21
    @3
    c2
    cexp
    co
    #
    caddc
    co
    #
    @23
    c1
    @24
    cc0
    @21
    caddc
    @24
    cc0
    c2
    cexp
    co
    cc0
    @3
    cc0
    c2
    cexp
    @1
    cc0
    wceq
    #
    @4
    @1
    cc0
    @1
    @11
    @1
    cr
    wcel
    @14
    @0
    resincl
    ax-mp
    @20
    gt0ne0ii
    neii
    @1
    @3
    cmul
    co
    #
    cc0
    wceq
    #
    @26
    @4
    wo
    c2
    cc0
    wceq
    #
    @28
    c2
    cc0
    2ne0
    neii
    c2
    @27
    cmul
    co
    #
    cc0
    wceq
    @29
    @28
    wo
    cpi
    csin
    cfv
    #
    @30
    cc0
    c2
    @0
    cmul
    co
    #
    csin
    cfv
    #
    @31
    @30
    @32
    cpi
    csin
    cpi
    c2
    cpi
    pire
    recni
    2cn
    2ne0
    divcan2i
    fveq2i
    @0
    cc
    wcel
    #
    @33
    @30
    wceq
    @0
    @14
    recni
    #
    @0
    sin2t
    ax-mp
    eqtr3i
    sinpi
    eqtr3i
    c2
    @27
    2cn
    @1
    @3
    @34
    @1
    cc
    wcel
    @35
    @0
    sincl
    ax-mp
    #
    @34
    @3
    cc
    wcel
    @35
    @0
    coscl
    ax-mp
    #
    mulcli
    mul0ori
    mpbi
    mtpor
    @1
    @3
    @36
    @37
    mul0ori
    mpbi
    mtpor
    #
    oveq1i
    sq0
    eqtri
    oveq2i
    @34
    @25
    c1
    wceq
    @35
    @0
    sincossq
    ax-mp
    eqtr3i
    @21
    @1
    @36
    sqcli
    addid1i
    3eqtr2ri
    @1
    c1
    @36
    ax-1cn
    sqeqori
    mpbi
    ori
    mt3
    @38
    pm3.2i
end
