include "cnp.mm"
include "wcel.mm"
include "c0.mm"
include "wpss.mm"
include "cnq.mm"
include "wa.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "wne.mm"
include "wn.mm"
include "wex.mm"
include "prpssnq.mm"
include "pssnel.mm"
include "crq.mm"
include "cfv.mm"
include "recclnq.mm"
include "nsmallnq.mm"
include "syl.mm"
include "adantr.mm"
include "recrecnq.mm"
include "eleq1d.mm"
include "notbid.mm"
include "anbi2d.mm"
include "fvex.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6bir.mm"
include "vex.mm"
include "breq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab2.mm"
include "syl6ibr.mm"
include "expcomd.mm"
include "imp.mm"
include "eximdv.mm"
include "mpd.mm"
include "n0.mm"
include "sylibr.mm"
include "exlimiv.mm"
include "3syl.mm"
include "0pss.mm"
include "wss.mm"
include "prn0.mm"
include "wb.mm"
include "elprnq.mm"
include "pm2.43i.mm"
include "dmrecnq.mm"
include "0nnq.mm"
include "ndmfvrcl.mm"
include "ltrnq.mm"
include "prcdnq.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "abeq2i.mm"
include "exanali.mm"
include "bitri.mm"
include "con2bii.mm"
include "sylib.mm"
include "jca.mm"
include "eximi.mm"
include "ex.mm"
include "exlimdv.mm"
include "nss.mm"
include "3imtr4g.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simpld.mm"
include "sylbi.mm"
include "ssriv.mm"
include "jctil.mm"
include "dfpss3.mm"
include "ltsonq.mm"
include "sotri.mm"
include "anim1d.mm"
include "com12.mm"
include "cab.mm"
include "nfe1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfv.mm"
include "nfrex.mm"
include "19.8a.mm"
include "adantll.mm"
include "simpll.mm"
include "expcom.mm"
include "ltbtwnnq.mm"
include "df-rex.mm"
include "impcom.mm"
include "exlimi.mm"
include "rgen.mm"
include "jctir.mm"
include "elnp.mm"

theorem reclem2pr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  assume reclempr.1: |- B = { x | E. y ( x <Q y /\ -. ( *Q ` y ) e. A ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint g x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint g y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint f z
  disjoint g z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint g w
  disjoint A w
  disjoint u v
  disjoint f v
  disjoint g v
  disjoint A v
  disjoint f u
  disjoint g u
  disjoint A u
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint B f
  disjoint B g
  assert |- ( A e. P. -> B e. P. )

  proof
    cA
    cnp
    wcel
    #
    c0
    cB
    wpss
    #
    cB
    cnq
    wpss
    #
    wa
    #
    vz
    cv
    #
    vx
    cv
    #
    cltq
    wbr
    #
    @4
    cB
    wcel
    #
    wi
    #
    vz
    wal
    #
    @5
    @4
    cltq
    wbr
    #
    vz
    cB
    wrex
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    cB
    cnp
    wcel
    @0
    @3
    @13
    @0
    @1
    @2
    @0
    cB
    c0
    wne
    #
    @1
    @0
    cA
    cnq
    wpss
    @5
    cnq
    wcel
    #
    @5
    cA
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    @14
    cA
    prpssnq
    vx
    cA
    cnq
    pssnel
    @18
    @14
    vx
    @18
    @7
    vz
    wex
    #
    @14
    @18
    @4
    @5
    crq
    cfv
    #
    cltq
    wbr
    #
    vz
    wex
    #
    @19
    @15
    @22
    @17
    @15
    @20
    cnq
    wcel
    #
    @22
    @5
    recclnq
    vz
    @20
    nsmallnq
    syl
    adantr
    @18
    @21
    @7
    vz
    @15
    @17
    @21
    @7
    wi
    @15
    @21
    @17
    @7
    @15
    @21
    @17
    wa
    #
    @4
    vy
    cv
    #
    cltq
    wbr
    #
    @25
    crq
    cfv
    #
    cA
    wcel
    #
    wn
    #
    wa
    #
    vy
    wex
    #
    @7
    @15
    @24
    @21
    @20
    crq
    cfv
    #
    cA
    wcel
    #
    wn
    #
    wa
    #
    @31
    @15
    @34
    @17
    @21
    @15
    @33
    @16
    @15
    @32
    @5
    cA
    @5
    recrecnq
    eleq1d
    notbid
    anbi2d
    @30
    @35
    vy
    @20
    @5
    crq
    fvex
    @25
    @20
    wceq
    #
    @26
    @21
    @29
    @34
    @25
    @20
    @4
    cltq
    breq2
    @36
    @28
    @33
    @36
    @27
    @32
    cA
    @25
    @20
    crq
    fveq2
    eleq1d
    notbid
    anbi12d
    spcev
    syl6bir
    @5
    @25
    cltq
    wbr
    #
    @29
    wa
    #
    vy
    wex
    #
    @31
    vx
    @4
    cB
    vz
    vex
    @5
    @4
    wceq
    #
    @38
    @30
    vy
    @40
    @37
    @26
    @29
    @5
    @4
    @25
    cltq
    breq1
    anbi1d
    exbidv
    reclempr.1
    elab2
    #
    syl6ibr
    expcomd
    imp
    eximdv
    mpd
    vz
    cB
    n0
    sylibr
    exlimiv
    3syl
    cB
    0pss
    sylibr
    @0
    cB
    cnq
    wss
    #
    cnq
    cB
    wss
    wn
    #
    wa
    @2
    @0
    @43
    @42
    @0
    cA
    c0
    wne
    #
    @43
    cA
    prn0
    @0
    @4
    cA
    wcel
    #
    vz
    wex
    @15
    @5
    cB
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    @44
    @43
    @0
    @45
    @49
    vz
    @0
    @45
    @49
    @0
    @45
    wa
    #
    @0
    @20
    cA
    wcel
    #
    wa
    #
    vx
    wex
    #
    @49
    @50
    @53
    @50
    @50
    @0
    @4
    crq
    cfv
    #
    crq
    cfv
    #
    cA
    wcel
    #
    wa
    #
    @53
    @50
    @4
    cnq
    wcel
    #
    @57
    @50
    wb
    cA
    @4
    elprnq
    @58
    @56
    @45
    @0
    @58
    @55
    @4
    cA
    @4
    recrecnq
    eleq1d
    anbi2d
    syl
    @52
    @57
    vx
    @54
    @4
    crq
    fvex
    @5
    @54
    wceq
    #
    @51
    @56
    @0
    @59
    @20
    @55
    cA
    @5
    @54
    crq
    fveq2
    eleq1d
    anbi2d
    spcev
    syl6bir
    pm2.43i
    @52
    @48
    vx
    @52
    @15
    @47
    @52
    @23
    @15
    cA
    @20
    elprnq
    @5
    cnq
    crq
    dmrecnq
    0nnq
    ndmfvrcl
    syl
    @52
    @37
    @28
    wi
    #
    vy
    wal
    #
    @47
    @52
    @60
    vy
    @37
    @27
    @20
    cltq
    wbr
    @52
    @28
    @5
    @25
    ltrnq
    cA
    @20
    @27
    prcdnq
    syl5bi
    alrimiv
    @46
    @61
    @46
    @39
    @61
    wn
    @39
    vx
    cB
    reclempr.1
    abeq2i
    #
    @37
    @28
    vy
    exanali
    bitri
    con2bii
    sylib
    jca
    eximi
    syl
    ex
    exlimdv
    vz
    cA
    n0
    vx
    cnq
    cB
    nss
    3imtr4g
    mpd
    vx
    cB
    cnq
    @46
    @39
    @15
    @62
    @38
    @15
    vy
    @37
    @15
    @29
    @37
    @15
    @25
    cnq
    wcel
    @5
    @25
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    adantr
    exlimiv
    sylbi
    ssriv
    jctil
    cB
    cnq
    dfpss3
    sylibr
    jca
    @12
    vx
    cB
    @46
    @9
    @11
    @46
    @8
    vz
    @6
    @46
    @7
    @6
    @39
    @31
    @46
    @7
    @6
    @38
    @30
    vy
    @6
    @37
    @26
    @29
    @6
    @37
    @26
    @4
    @5
    @25
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    ex
    anim1d
    eximdv
    @62
    @41
    3imtr4g
    com12
    alrimiv
    @46
    @39
    @11
    @62
    @38
    @11
    vy
    @10
    vy
    vz
    cB
    vy
    cB
    @39
    vx
    cab
    reclempr.1
    @39
    vy
    vx
    @38
    vy
    nfe1
    nfab
    nfcxfr
    @10
    vy
    nfv
    nfrex
    @29
    @37
    @11
    @29
    @10
    @26
    wa
    #
    vz
    wex
    @7
    @10
    wa
    #
    vz
    wex
    @37
    @11
    @29
    @63
    @64
    vz
    @63
    @29
    @64
    @63
    @29
    wa
    @7
    @10
    @26
    @29
    @7
    @10
    @30
    @31
    @7
    @30
    vy
    19.8a
    @41
    sylibr
    adantll
    @10
    @26
    @29
    simpll
    jca
    expcom
    eximdv
    vz
    @5
    @25
    ltbtwnnq
    @10
    vz
    cB
    df-rex
    3imtr4g
    impcom
    exlimi
    sylbi
    jca
    rgen
    jctir
    vx
    vz
    cB
    elnp
    sylibr
end
