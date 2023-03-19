include "c3.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "c5.mm"
include "cdp.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "wceq.mm"
include "3re.mm"
include "2re.mm"
include "2ne0.mm"
include "redivcli.mm"
include "recni.mm"
include "cn0.mm"
include "cr.mm"
include "1nn0.mm"
include "5re.mm"
include "dpcl.mm"
include "mp2an.mm"
include "2cnne0.mm"
include "3pm3.2i.mm"
include "caddc.mm"
include "5nn0.mm"
include "3nn0.mm"
include "0nn0.mm"
include "cdc.mm"
include "eqid.mm"
include "df-2.mm"
include "oveq1i.mm"
include "2p1e3.mm"
include "eqtr3i.mm"
include "5p5e10.mm"
include "decaddc.mm"
include "dpadd.mm"
include "dp0u.mm"
include "eqtri.mm"
include "times2i.mm"
include "simpli.mm"
include "divcan1i.mm"
include "3eqtr4ri.mm"
include "mulcan2.mm"
include "biimpa.mm"

theorem threehalves



  assert |- ( 3 / 2 ) = ( 1 . 5 )

  proof
    c3
    c2
    cdiv
    co
    #
    cc
    wcel
    #
    c1
    c5
    cdp
    co
    #
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    #
    w3a
    #
    @0
    c2
    cmul
    co
    #
    @2
    c2
    cmul
    co
    #
    wceq
    #
    @0
    @2
    wceq
    #
    @1
    @3
    @6
    @0
    c3
    c2
    3re
    2re
    2ne0
    redivcli
    recni
    @2
    c1
    cn0
    wcel
    c5
    cr
    wcel
    @2
    cr
    wcel
    1nn0
    5re
    c1
    c5
    dpcl
    mp2an
    recni
    #
    2cnne0
    3pm3.2i
    @2
    @2
    caddc
    co
    #
    c3
    @9
    @8
    @13
    c3
    cc0
    cdp
    co
    c3
    c1
    c5
    c1
    c5
    c3
    cc0
    1nn0
    5nn0
    1nn0
    5nn0
    3nn0
    0nn0
    c1
    c5
    c1
    c5
    c3
    cc0
    c1
    c5
    cdc
    #
    @14
    1nn0
    5nn0
    1nn0
    5nn0
    @14
    eqid
    #
    @15
    c2
    c1
    caddc
    co
    c1
    c1
    caddc
    co
    #
    c1
    caddc
    co
    c3
    c2
    @16
    c1
    caddc
    df-2
    oveq1i
    2p1e3
    eqtr3i
    0nn0
    5p5e10
    decaddc
    dpadd
    c3
    3nn0
    dp0u
    eqtri
    @2
    @12
    times2i
    c3
    c2
    c3
    3re
    recni
    @4
    @5
    2cnne0
    simpli
    2ne0
    divcan1i
    3eqtr4ri
    @7
    @10
    @11
    @0
    @2
    c2
    mulcan2
    biimpa
    mp2an
end
