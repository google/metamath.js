include "con0.mm"
include "cv.mm"
include "word.mm"
include "cab.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "df-on.mm"
include "wss.mm"
include "wne.mm"
include "tz7.7.mm"
include "df-pss.mm"
include "syl6bbr.mm"
include "exbiri.mm"
include "com23.mm"
include "impd.mm"
include "alrimiv.mm"
include "cep.mm"
include "wwe.mm"
include "wn.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "dfon2lem3.mm"
include "ax-mp.mm"
include "simpld.mm"
include "wfr.mm"
include "weq.mm"
include "w3o.mm"
include "dfon2lem7.mm"
include "ralrimiv.mm"
include "dfon2lem9.mm"
include "psseq2.mm"
include "anbi1d.mm"
include "elequ2.mm"
include "imbi12d.mm"
include "albidv.mm"
include "psseq1.mm"
include "treq.mm"
include "anbi12d.mm"
include "elequ1.mm"
include "cbvalv.mm"
include "syl6bb.mm"
include "rspccv.mm"
include "anim12d.mm"
include "dfon2lem5.mm"
include "syl6.mm"
include "ralrimivv.mm"
include "jca.mm"
include "syl.mm"
include "wbr.mm"
include "dfwe2.mm"
include "epel.mm"
include "biid.mm"
include "3orbi123i.mm"
include "2ralbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "sylibr.mm"
include "df-ord.mm"
include "sylanbrc.mm"
include "impbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfon2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint t x
  disjoint u x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint w z
  disjoint t z
  disjoint u z
  disjoint v z
  disjoint t w
  disjoint u w
  disjoint v w
  disjoint t u
  disjoint t v
  disjoint u v
  assert |- On = { x | A. y ( ( y C. x /\ Tr y ) -> y e. x ) }

  proof
    con0
    vx
    cv
    #
    word
    #
    vx
    cab
    vy
    cv
    #
    @0
    wpss
    #
    @2
    wtr
    #
    wa
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    cab
    vx
    df-on
    @1
    @7
    vx
    @1
    @7
    @1
    @6
    vy
    @1
    @3
    @4
    @5
    @1
    @4
    @3
    @5
    @1
    @4
    @5
    @3
    @1
    @4
    wa
    @5
    @2
    @0
    wss
    @2
    @0
    wne
    wa
    @3
    @0
    @2
    tz7.7
    @2
    @0
    df-pss
    syl6bbr
    exbiri
    com23
    impd
    alrimiv
    @7
    @0
    wtr
    #
    @0
    cep
    wwe
    #
    @1
    @7
    @8
    vz
    vz
    wel
    wn
    vz
    @0
    wral
    #
    @0
    cvv
    wcel
    @7
    @8
    @10
    wa
    wi
    vx
    vex
    #
    vy
    vz
    @0
    cvv
    dfon2lem3
    ax-mp
    simpld
    @7
    @0
    cep
    wfr
    #
    vz
    vw
    wel
    #
    vz
    vw
    weq
    #
    vw
    vz
    wel
    #
    w3o
    #
    vw
    @0
    wral
    vz
    @0
    wral
    #
    wa
    #
    @9
    @7
    vu
    cv
    #
    vt
    cv
    #
    wpss
    #
    @19
    wtr
    #
    wa
    #
    vu
    vt
    wel
    #
    wi
    #
    vu
    wal
    #
    vt
    @0
    wral
    #
    @18
    @7
    @26
    vt
    @0
    vy
    vu
    @0
    @20
    @11
    dfon2lem7
    ralrimiv
    @27
    @12
    @17
    vt
    vu
    @0
    dfon2lem9
    @27
    @16
    vz
    vw
    @0
    @0
    @27
    vz
    vx
    wel
    #
    vw
    vx
    wel
    #
    wa
    vv
    cv
    #
    vz
    cv
    #
    wpss
    #
    @30
    wtr
    #
    wa
    #
    vv
    vz
    wel
    #
    wi
    #
    vv
    wal
    #
    @2
    vw
    cv
    #
    wpss
    #
    @4
    wa
    #
    vy
    vw
    wel
    #
    wi
    #
    vy
    wal
    #
    wa
    @16
    @27
    @28
    @37
    @29
    @43
    @26
    @37
    vt
    @31
    @0
    vt
    vz
    weq
    #
    @26
    @19
    @31
    wpss
    #
    @22
    wa
    #
    vu
    vz
    wel
    #
    wi
    #
    vu
    wal
    @37
    @44
    @25
    @48
    vu
    @44
    @23
    @46
    @24
    @47
    @44
    @21
    @45
    @22
    @20
    @31
    @19
    psseq2
    anbi1d
    vt
    vz
    vu
    elequ2
    imbi12d
    albidv
    @48
    @36
    vu
    vv
    vu
    vv
    weq
    #
    @46
    @34
    @47
    @35
    @49
    @45
    @32
    @22
    @33
    @19
    @30
    @31
    psseq1
    @19
    @30
    treq
    anbi12d
    vu
    vv
    vz
    elequ1
    imbi12d
    cbvalv
    syl6bb
    rspccv
    @26
    @43
    vt
    @38
    @0
    vt
    vw
    weq
    #
    @26
    @19
    @38
    wpss
    #
    @22
    wa
    #
    vu
    vw
    wel
    #
    wi
    #
    vu
    wal
    @43
    @50
    @25
    @54
    vu
    @50
    @23
    @52
    @24
    @53
    @50
    @21
    @51
    @22
    @20
    @38
    @19
    psseq2
    anbi1d
    vt
    vw
    vu
    elequ2
    imbi12d
    albidv
    @54
    @42
    vu
    vy
    vu
    vy
    weq
    #
    @52
    @40
    @53
    @41
    @55
    @51
    @39
    @22
    @4
    @19
    @2
    @38
    psseq1
    @19
    @2
    treq
    anbi12d
    vu
    vy
    vw
    elequ1
    imbi12d
    cbvalv
    syl6bb
    rspccv
    anim12d
    vv
    vy
    @31
    @38
    vz
    vex
    vw
    vex
    dfon2lem5
    syl6
    ralrimivv
    jca
    syl
    @9
    @12
    @31
    @38
    cep
    wbr
    #
    @14
    @38
    @31
    cep
    wbr
    #
    w3o
    #
    vw
    @0
    wral
    vz
    @0
    wral
    #
    wa
    @18
    vz
    vw
    @0
    cep
    dfwe2
    @59
    @17
    @12
    @58
    @16
    vz
    vw
    @0
    @0
    @56
    @13
    @14
    @14
    @57
    @15
    vz
    vw
    epel
    @14
    biid
    vw
    vz
    epel
    3orbi123i
    2ralbii
    anbi2i
    bitri
    sylibr
    @0
    df-ord
    sylanbrc
    impbii
    abbii
    eqtri
end
