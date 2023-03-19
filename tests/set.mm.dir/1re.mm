include "cv.mm"
include "wne.mm"
include "cr.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ax-1ne0.mm"
include "wceq.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cnre.mm"
include "ax-mp.mm"
include "neeq1.mm"
include "biimpcd.mm"
include "0cn.mm"
include "neeq2.mm"
include "reximdv.mm"
include "syl6mpi.mm"
include "mpi.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "ioran.mm"
include "df-ne.mm"
include "con2bii.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "id.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "sylbi.mm"
include "necon1ai.mm"
include "wi.mm"
include "rspc2ev.mm"
include "3expia.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "jaod.mm"
include "syl5.mm"
include "rexlimdvva.mm"
include "rexlimivv.mm"
include "mp2b.mm"
include "eqtr3.mm"
include "ex.mm"
include "necon3d.mm"
include "rspcev.mm"
include "expcom.mm"
include "syl6.mm"
include "com23.mm"
include "adantld.mm"
include "adantrd.mm"
include "a1dd.mm"
include "pm2.61ine.mm"
include "ax-rrecex.mm"
include "remulcl.mm"
include "adantlr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "rexlimiva.mm"

theorem 1re
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- 1 e. RR

  proof
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    vz
    cv
    #
    cc0
    wne
    #
    vz
    cr
    wrex
    #
    c1
    cr
    wcel
    #
    c1
    cc0
    wne
    #
    va
    cv
    #
    ci
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    vc
    cv
    #
    ci
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wne
    #
    vd
    cr
    wrex
    #
    vc
    cr
    wrex
    #
    vb
    cr
    wrex
    #
    va
    cr
    wrex
    #
    @3
    ax-1ne0
    @8
    c1
    @12
    wceq
    #
    vb
    cr
    wrex
    #
    va
    cr
    wrex
    #
    @21
    c1
    cc
    wcel
    @24
    ax-1cn
    va
    vb
    c1
    cnre
    ax-mp
    @8
    @23
    @20
    va
    cr
    @8
    @22
    @19
    vb
    cr
    @8
    @22
    @12
    cc0
    wne
    #
    cc0
    @16
    wceq
    #
    vd
    cr
    wrex
    #
    vc
    cr
    wrex
    #
    @19
    @22
    @8
    @25
    c1
    @12
    cc0
    neeq1
    biimpcd
    cc0
    cc
    wcel
    @28
    0cn
    vc
    vd
    cc0
    cnre
    ax-mp
    @25
    @27
    @18
    vc
    cr
    @25
    @26
    @17
    vd
    cr
    @26
    @25
    @17
    cc0
    @16
    @12
    neeq2
    biimpcd
    reximdv
    reximdv
    syl6mpi
    reximdv
    reximdv
    mpi
    @19
    @3
    va
    vb
    cr
    cr
    @9
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    wa
    #
    @17
    @3
    vc
    vd
    cr
    cr
    @17
    @9
    @13
    wne
    #
    @10
    @14
    wne
    #
    wo
    #
    @31
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    wa
    wa
    #
    @3
    @34
    @12
    @16
    @34
    wn
    #
    @9
    @13
    wceq
    #
    @10
    @14
    wceq
    #
    wa
    #
    @12
    @16
    wceq
    @38
    @32
    wn
    #
    @33
    wn
    #
    wa
    @41
    @32
    @33
    ioran
    @39
    @42
    @40
    @43
    @32
    @39
    @9
    @13
    df-ne
    con2bii
    @33
    @40
    @10
    @14
    df-ne
    con2bii
    anbi12i
    bitr4i
    @39
    @40
    @9
    @13
    @11
    @15
    caddc
    @39
    id
    @10
    @14
    ci
    cmul
    oveq2
    oveqan12d
    sylbi
    necon1ai
    @37
    @32
    @3
    @33
    @29
    @35
    @32
    @3
    wi
    @30
    @36
    @29
    @35
    @32
    @3
    @2
    @32
    @9
    @1
    wne
    vx
    vy
    @9
    @13
    cr
    cr
    @0
    @9
    @1
    neeq1
    @1
    @13
    @9
    neeq2
    rspc2ev
    3expia
    ad2ant2r
    @30
    @36
    @33
    @3
    wi
    @29
    @35
    @30
    @36
    @33
    @3
    @2
    @33
    @10
    @1
    wne
    vx
    vy
    @10
    @14
    cr
    cr
    @0
    @10
    @1
    neeq1
    @1
    @14
    @10
    neeq2
    rspc2ev
    3expia
    ad2ant2l
    jaod
    syl5
    rexlimdvva
    rexlimivv
    mp2b
    @2
    @6
    vx
    vy
    cr
    cr
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @2
    @6
    wi
    #
    wi
    @0
    cc0
    @0
    cc0
    wceq
    #
    @45
    @47
    @44
    @48
    @2
    @45
    @6
    @48
    @2
    @1
    cc0
    wne
    #
    @45
    @6
    wi
    @48
    @1
    cc0
    @0
    @1
    @48
    @1
    cc0
    wceq
    @0
    @1
    wceq
    @0
    @1
    cc0
    eqtr3
    ex
    necon3d
    @45
    @49
    @6
    @5
    @49
    vz
    @1
    cr
    @4
    @1
    cc0
    neeq1
    rspcev
    expcom
    syl6
    com23
    adantld
    @0
    cc0
    wne
    #
    @46
    @6
    @2
    @50
    @44
    @6
    @45
    @44
    @50
    @6
    @5
    @50
    vz
    @0
    cr
    @4
    @0
    cc0
    neeq1
    rspcev
    expcom
    adantrd
    a1dd
    pm2.61ine
    rexlimivv
    @5
    @7
    vz
    cr
    @4
    cr
    wcel
    #
    @5
    wa
    #
    @4
    @0
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    @7
    vx
    @4
    ax-rrecex
    @52
    @54
    @7
    vx
    cr
    @52
    @44
    wa
    @53
    cr
    wcel
    #
    @54
    @7
    @51
    @44
    @55
    @5
    @4
    @0
    remulcl
    adantlr
    @53
    c1
    cr
    eleq1
    syl5ibcom
    rexlimdva
    mpd
    rexlimiva
    mp2b
end
