include "ci.mm"
include "clog.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ce.mm"
include "efhalfpi.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "crn.mm"
include "wb.mm"
include "ax-icn.mm"
include "ine0.mm"
include "cneg.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "halfpire.mm"
include "recni.mm"
include "mulcli.mm"
include "pipos.mm"
include "cr.mm"
include "pire.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "halfpos2.mm"
include "renegcli.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "cre.mm"
include "reim.mm"
include "rere.mm"
include "eqtr3i.mm"
include "breqtrri.mm"
include "wtru.mm"
include "caddc.mm"
include "a1i.mm"
include "ltaddposd.mm"
include "mpbii.mm"
include "picn.mm"
include "times2i.mm"
include "syl6breqr.mm"
include "crp.mm"
include "2rp.mm"
include "ltdivmul2d.mm"
include "mpbird.mm"
include "trud.mm"
include "ltleii.mm"
include "eqbrtri.mm"
include "ellogrn.mm"
include "mpbir3an.mm"
include "logeftb.mm"
include "mp3an.mm"
include "mpbir.mm"

theorem logi



  assert |- ( log ` _i ) = ( _i x. ( _pi / 2 ) )

  proof
    ci
    clog
    cfv
    ci
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    wceq
    #
    @1
    ce
    cfv
    ci
    wceq
    #
    efhalfpi
    ci
    cc
    wcel
    ci
    cc0
    wne
    @1
    clog
    crn
    wcel
    #
    @2
    @3
    wb
    ax-icn
    ine0
    @4
    @1
    cc
    wcel
    cpi
    cneg
    #
    @1
    cim
    cfv
    #
    clt
    wbr
    @6
    cpi
    cle
    wbr
    ci
    @0
    ax-icn
    @0
    halfpire
    recni
    #
    mulcli
    @5
    @0
    @6
    clt
    @5
    cc0
    clt
    wbr
    #
    cc0
    @0
    clt
    wbr
    #
    @5
    @0
    clt
    wbr
    cc0
    cpi
    clt
    wbr
    #
    @8
    pipos
    cpi
    cr
    wcel
    #
    @10
    @8
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    @10
    @9
    pipos
    @11
    @10
    @9
    wb
    pire
    cpi
    halfpos2
    ax-mp
    mpbi
    @5
    cc0
    @0
    cpi
    pire
    renegcli
    0re
    halfpire
    lttri
    mp2an
    @0
    cre
    cfv
    #
    @6
    @0
    @0
    cc
    wcel
    @12
    @6
    wceq
    @7
    @0
    reim
    ax-mp
    @0
    cr
    wcel
    @12
    @0
    wceq
    halfpire
    @0
    rere
    ax-mp
    eqtr3i
    #
    breqtrri
    @6
    @0
    cpi
    cle
    @13
    @0
    cpi
    halfpire
    pire
    @0
    cpi
    clt
    wbr
    #
    wtru
    @14
    cpi
    cpi
    c2
    cmul
    co
    #
    clt
    wbr
    wtru
    cpi
    cpi
    cpi
    caddc
    co
    #
    @15
    clt
    wtru
    @10
    cpi
    @16
    clt
    wbr
    pipos
    wtru
    cpi
    cpi
    @11
    wtru
    pire
    a1i
    #
    @17
    ltaddposd
    mpbii
    cpi
    picn
    times2i
    syl6breqr
    wtru
    cpi
    cpi
    c2
    @17
    @17
    c2
    crp
    wcel
    wtru
    2rp
    a1i
    ltdivmul2d
    mpbird
    trud
    ltleii
    eqbrtri
    @1
    ellogrn
    mpbir3an
    ci
    @1
    logeftb
    mp3an
    mpbir
end
