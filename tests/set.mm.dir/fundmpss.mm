include "wfun.mm"
include "wpss.mm"
include "cdm.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "pssss.mm"
include "dmss.mm"
include "syl.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cdif.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "pssdif.mm"
include "n0.mm"
include "sylib.mm"
include "adantl.mm"
include "wrel.mm"
include "funrel.mm"
include "reldif.mm"
include "cop.mm"
include "wceq.mm"
include "elrel.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "biimpcd.mm"
include "2eximdv.mm"
include "mpd.mm"
include "ex.mm"
include "adantr.mm"
include "difss.mm"
include "ssbri.mm"
include "eximi.mm"
include "brdif.mm"
include "simprbi.mm"
include "ssbrd.mm"
include "ad2antlr.mm"
include "simplbi.mm"
include "weq.mm"
include "wal.mm"
include "dffun2.mm"
include "2sp.mm"
include "sps.mm"
include "breq2.mm"
include "biimprd.mm"
include "syl6.mm"
include "expd.mm"
include "syl5.mm"
include "imp.mm"
include "adantlr.mm"
include "com23.mm"
include "mpdd.mm"
include "exlimdv.mm"
include "mtod.mm"
include "jcad.mm"
include "eximdv.mm"
include "syld.mm"
include "nss.mm"
include "vex.mm"
include "eldm.mm"
include "notbii.mm"
include "anbi12i.mm"
include "exbii.mm"
include "bitri.mm"
include "sylibr.mm"
include "dfpss3.mm"
include "syl6ibr.mm"

theorem fundmpss
  let cF: class F
  let cG: class G
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Fun G -> ( F C. G -> dom F C. dom G ) )

  proof
    cG
    wfun
    #
    cF
    cG
    wpss
    #
    cF
    cdm
    #
    cG
    cdm
    #
    wss
    #
    @3
    @2
    wss
    wn
    #
    wa
    @2
    @3
    wpss
    @0
    @1
    @4
    @5
    @1
    @4
    wi
    @0
    @1
    cF
    cG
    wss
    @4
    cF
    cG
    pssss
    #
    cF
    cG
    dmss
    syl
    a1i
    @0
    @1
    @5
    @0
    @1
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    wbr
    #
    vy
    wex
    #
    @8
    vz
    cv
    #
    cF
    wbr
    #
    vz
    wex
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    @5
    @7
    vp
    cv
    #
    cG
    cF
    cdif
    #
    wcel
    #
    vp
    wex
    #
    @17
    @1
    @21
    @0
    @1
    @19
    c0
    wne
    @21
    cF
    cG
    pssdif
    vp
    @19
    n0
    sylib
    adantl
    @7
    @20
    @17
    vp
    @7
    @20
    @8
    @9
    @19
    wbr
    #
    vy
    wex
    #
    vx
    wex
    #
    @17
    @0
    @20
    @24
    wi
    #
    @1
    @0
    @19
    wrel
    #
    @25
    @0
    cG
    wrel
    #
    @26
    cG
    funrel
    cG
    cF
    reldif
    syl
    @26
    @20
    @24
    @26
    @20
    wa
    #
    @18
    @8
    @9
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    @24
    vx
    vy
    @18
    @19
    elrel
    @28
    @30
    @22
    vx
    vy
    @20
    @30
    @22
    wi
    @26
    @30
    @20
    @22
    @30
    @20
    @29
    @19
    wcel
    @22
    @18
    @29
    @19
    eleq1
    @8
    @9
    @19
    df-br
    syl6bbr
    biimpcd
    adantl
    2eximdv
    mpd
    ex
    syl
    adantr
    @7
    @23
    @16
    vx
    @7
    @23
    @11
    @15
    @23
    @11
    wi
    @7
    @22
    @10
    vy
    @19
    cG
    @8
    @9
    cG
    cF
    difss
    ssbri
    eximi
    a1i
    @7
    @22
    @15
    vy
    @7
    @22
    @15
    @7
    @22
    wa
    #
    @14
    @8
    @9
    cF
    wbr
    #
    @22
    @32
    wn
    #
    @7
    @22
    @10
    @33
    @8
    @9
    cG
    cF
    brdif
    #
    simprbi
    adantl
    @31
    @13
    @32
    vz
    @31
    @13
    @8
    @12
    cG
    wbr
    #
    @32
    @1
    @13
    @35
    wi
    @0
    @22
    @1
    cF
    cG
    @8
    @12
    @6
    ssbrd
    ad2antlr
    @31
    @35
    @13
    @32
    @0
    @22
    @35
    @13
    @32
    wi
    #
    wi
    #
    @1
    @0
    @22
    @37
    @22
    @10
    @0
    @37
    @22
    @10
    @33
    @34
    simplbi
    @0
    @10
    @35
    @36
    @0
    @10
    @35
    wa
    #
    vy
    vz
    weq
    #
    @36
    @0
    @38
    @39
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    @40
    @0
    @27
    @42
    vx
    vy
    vz
    cG
    dffun2
    simprbi
    @41
    @40
    vx
    @40
    vy
    vz
    2sp
    sps
    syl
    @39
    @32
    @13
    @9
    @12
    @8
    cF
    breq2
    biimprd
    syl6
    expd
    syl5
    imp
    adantlr
    com23
    mpdd
    exlimdv
    mtod
    ex
    exlimdv
    jcad
    eximdv
    syld
    exlimdv
    mpd
    @5
    @8
    @3
    wcel
    #
    @8
    @2
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    @17
    vx
    @3
    @2
    nss
    @46
    @16
    vx
    @43
    @11
    @45
    @15
    vy
    @8
    cG
    vx
    vex
    #
    eldm
    @44
    @14
    vz
    @8
    cF
    @47
    eldm
    notbii
    anbi12i
    exbii
    bitri
    sylibr
    ex
    jcad
    @2
    @3
    dfpss3
    syl6ibr
end
