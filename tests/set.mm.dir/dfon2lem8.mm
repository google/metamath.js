include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "cint.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "vex.mm"
include "dfon2lem3.mm"
include "ax-mp.mm"
include "simpld.mm"
include "ralimi.mm"
include "trint.mm"
include "syl.mm"
include "adantl.mm"
include "cuni.mm"
include "dfon2lem7.mm"
include "alrimiv.mm"
include "df-ral.mm"
include "19.21v.mm"
include "albii.mm"
include "bitr4i.mm"
include "impexp.mm"
include "2albii.mm"
include "wrex.mm"
include "eluni2.mm"
include "biimpi.mm"
include "imim1i.mm"
include "alimi.mm"
include "alcom.mm"
include "wex.mm"
include "19.23v.mm"
include "df-rex.mm"
include "imbi1i.mm"
include "bitri.mm"
include "3imtr4i.mm"
include "sylbir.mm"
include "sylbi.mm"
include "wss.mm"
include "intssuni.mm"
include "ssralv.mm"
include "adantr.mm"
include "mpd.mm"
include "dfon2lem6.mm"
include "intex.mm"
include "imp.mm"
include "simprd.mm"
include "untelirr.mm"
include "adantlr.mm"
include "wceq.mm"
include "risset.mm"
include "notbii.mm"
include "ralnex.mm"
include "eqcom.mm"
include "psseq2.mm"
include "anbi1d.mm"
include "elequ2.mm"
include "imbi12d.mm"
include "albidv.mm"
include "rspccv.mm"
include "intss1.mm"
include "dfpss2.mm"
include "psseq1.mm"
include "treq.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "spcgv.mm"
include "expd.mm"
include "syl5bir.mm"
include "exp4b.mm"
include "com45.mm"
include "com23.mm"
include "syl5.mm"
include "mpdd.mm"
include "mpid.mm"
include "syl7bi.mm"
include "ralrimiv.mm"
include "ralim.mm"
include "syl5bi.mm"
include "wb.mm"
include "elintg.mm"
include "ad2antrr.mm"
include "sylibrd.mm"
include "mt3d.mm"
include "ex.mm"
include "ancld.mm"
include "mp2and.mm"

theorem dfon2lem8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vt: setvar t

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A t
  disjoint w x
  disjoint t x
  disjoint w y
  disjoint t y
  disjoint w z
  disjoint t z
  disjoint t w
  assert |- ( ( A =/= (/) /\ A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x ) ) -> ( A. z ( ( z C. |^| A /\ Tr z ) -> z e. |^| A ) /\ |^| A e. A ) )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    wpss
    #
    @1
    wtr
    #
    wa
    #
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
    cA
    wral
    #
    wa
    #
    cA
    cint
    #
    wtr
    #
    vt
    cv
    #
    vw
    cv
    #
    wpss
    @13
    wtr
    wa
    vt
    vw
    wel
    wi
    vt
    wal
    #
    vw
    @11
    wral
    #
    vz
    cv
    #
    @11
    wpss
    @17
    wtr
    wa
    @17
    @11
    wcel
    wi
    vz
    wal
    #
    @11
    cA
    wcel
    #
    wa
    #
    @9
    @12
    @0
    @9
    @2
    wtr
    #
    vx
    cA
    wral
    @12
    @8
    @21
    vx
    cA
    @8
    @21
    vz
    vz
    wel
    wn
    vz
    @2
    wral
    #
    @2
    cvv
    wcel
    @8
    @21
    @22
    wa
    wi
    vx
    vex
    #
    vy
    vz
    @2
    cvv
    dfon2lem3
    ax-mp
    simpld
    ralimi
    vx
    cA
    trint
    syl
    adantl
    @10
    @15
    vw
    cA
    cuni
    #
    wral
    #
    @16
    @9
    @25
    @0
    @9
    vw
    vx
    wel
    #
    @15
    wi
    #
    vw
    wal
    #
    vx
    cA
    wral
    #
    @25
    @8
    @28
    vx
    cA
    @8
    @27
    vw
    vy
    vt
    @2
    @14
    @23
    dfon2lem7
    alrimiv
    ralimi
    @29
    @2
    cA
    wcel
    #
    @27
    wi
    #
    vw
    wal
    #
    vx
    wal
    #
    @25
    @29
    @30
    @28
    wi
    #
    vx
    wal
    @33
    @28
    vx
    cA
    df-ral
    @32
    @34
    vx
    @30
    @27
    vw
    19.21v
    albii
    bitr4i
    @33
    @30
    @26
    wa
    #
    @15
    wi
    #
    vw
    wal
    vx
    wal
    #
    @25
    @36
    @31
    vx
    vw
    @30
    @26
    @15
    impexp
    2albii
    @26
    vx
    cA
    wrex
    #
    @15
    wi
    #
    vw
    wal
    #
    @14
    @24
    wcel
    #
    @15
    wi
    #
    vw
    wal
    @37
    @25
    @39
    @42
    vw
    @41
    @38
    @15
    @41
    @38
    vx
    @14
    cA
    eluni2
    biimpi
    imim1i
    alimi
    @37
    @36
    vx
    wal
    #
    vw
    wal
    @40
    @36
    vx
    vw
    alcom
    @43
    @39
    vw
    @43
    @35
    vx
    wex
    #
    @15
    wi
    @39
    @35
    @15
    vx
    19.23v
    @38
    @44
    @15
    @26
    vx
    cA
    df-rex
    imbi1i
    bitr4i
    albii
    bitri
    @15
    vw
    @24
    df-ral
    3imtr4i
    sylbir
    sylbi
    syl
    adantl
    @0
    @25
    @16
    wi
    #
    @9
    @0
    @11
    @24
    wss
    @45
    cA
    intssuni
    @15
    vw
    @11
    @24
    ssralv
    syl
    adantr
    mpd
    @12
    @16
    wa
    @18
    @10
    @20
    vw
    vz
    vt
    @11
    dfon2lem6
    @10
    @18
    @19
    @10
    @18
    @19
    @10
    @18
    wa
    #
    @19
    @11
    @11
    wcel
    #
    @0
    @18
    @47
    wn
    #
    @9
    @0
    @18
    wa
    #
    vt
    vt
    wel
    wn
    vt
    @11
    wral
    #
    @48
    @49
    @12
    @50
    @0
    @18
    @12
    @50
    wa
    #
    @0
    @11
    cvv
    wcel
    #
    @18
    @51
    wi
    cA
    intex
    #
    vz
    vt
    @11
    cvv
    dfon2lem3
    sylbi
    imp
    #
    simprd
    vt
    @11
    untelirr
    syl
    adantlr
    @46
    @19
    wn
    #
    @11
    @13
    wcel
    #
    vt
    cA
    wral
    #
    @47
    @55
    @13
    @11
    wceq
    #
    wn
    #
    vt
    cA
    wral
    #
    @46
    @57
    @55
    @58
    vt
    cA
    wrex
    #
    wn
    @60
    @19
    @61
    vt
    @11
    cA
    risset
    notbii
    @58
    vt
    cA
    ralnex
    bitr4i
    @46
    @59
    @56
    wi
    #
    vt
    cA
    wral
    @60
    @57
    wi
    @46
    @62
    vt
    cA
    @59
    @11
    @13
    wceq
    #
    wn
    #
    @46
    @13
    cA
    wcel
    #
    @56
    @58
    @63
    @13
    @11
    eqcom
    notbii
    @46
    @65
    @12
    @64
    @56
    wi
    #
    @0
    @18
    @12
    @9
    @49
    @12
    @50
    @54
    simpld
    adantlr
    @10
    @65
    @12
    @66
    wi
    #
    wi
    @18
    @10
    @65
    @1
    @13
    wpss
    #
    @4
    wa
    #
    vy
    vt
    wel
    #
    wi
    #
    vy
    wal
    #
    @67
    @9
    @65
    @72
    wi
    @0
    @8
    @72
    vx
    @13
    cA
    @2
    @13
    wceq
    #
    @7
    @71
    vy
    @73
    @5
    @69
    @6
    @70
    @73
    @3
    @68
    @4
    @2
    @13
    @1
    psseq2
    anbi1d
    vx
    vt
    vy
    elequ2
    imbi12d
    albidv
    rspccv
    adantl
    @0
    @65
    @72
    @67
    wi
    #
    wi
    @9
    @65
    @11
    @13
    wss
    #
    @0
    @74
    @13
    cA
    intss1
    @0
    @72
    @75
    @67
    @0
    @72
    @75
    @64
    @12
    @56
    @0
    @72
    @75
    @64
    @12
    @56
    wi
    #
    @75
    @64
    wa
    @11
    @13
    wpss
    #
    @0
    @72
    wa
    #
    @76
    @11
    @13
    dfpss2
    @78
    @77
    @12
    @56
    @0
    @72
    @77
    @12
    wa
    #
    @56
    wi
    #
    @0
    @52
    @72
    @80
    wi
    @53
    @71
    @80
    vy
    @11
    cvv
    @1
    @11
    wceq
    #
    @69
    @79
    @70
    @56
    @81
    @68
    @77
    @4
    @12
    @1
    @11
    @13
    psseq1
    @1
    @11
    treq
    anbi12d
    @1
    @11
    @13
    eleq1
    imbi12d
    spcgv
    sylbi
    imp
    expd
    syl5bir
    exp4b
    com45
    com23
    syl5
    adantr
    mpdd
    adantr
    mpid
    syl7bi
    ralrimiv
    @59
    @56
    vt
    cA
    ralim
    syl
    syl5bi
    @0
    @47
    @57
    wb
    #
    @9
    @18
    @0
    @52
    @82
    @53
    vt
    @11
    cA
    cvv
    elintg
    sylbi
    ad2antrr
    sylibrd
    mt3d
    ex
    ancld
    syl5
    mp2and
end
