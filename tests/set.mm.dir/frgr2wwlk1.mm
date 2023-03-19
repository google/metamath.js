include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "weu.mm"
include "c0.mm"
include "wi.mm"
include "wal.mm"
include "frgr2wwlkn0.mm"
include "cs3.mm"
include "wrex.mm"
include "elwwlks2ons3.mm"
include "anbi12i.mm"
include "wreu.mm"
include "frgr2wwlkeu.mm"
include "wral.mm"
include "s3eq2.mm"
include "eleq1d.mm"
include "reu4.mm"
include "anbi1d.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "equequ2.mm"
include "rspc2va.mm"
include "pm3.35.mm"
include "equcoms.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq12.mm"
include "adantl.mm"
include "mpbird.mm"
include "equcomd.mm"
include "ex.mm"
include "syl.mm"
include "com23.mm"
include "exp4b.mm"
include "com13.mm"
include "imp.mm"
include "expcom.mm"
include "simplbiim.mm"
include "impl.mm"
include "rexlimdva.mm"
include "impd.mm"
include "syl5bi.mm"
include "alrimivv.mm"
include "eqeuel.mm"
include "syl2anc.mm"
include "cvv.mm"
include "ovex.mm"
include "euhash1.mm"
include "mp1i.mm"

theorem frgr2wwlk1
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vd: setvar d
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume frgr2wwlkeu.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ ( A e. V /\ B e. V ) /\ A =/= B ) -> ( # ` ( A ( 2 WWalksNOn G ) B ) ) = 1 )

  proof
    cG
    cfrgr
    wcel
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cA
    cB
    wne
    w3a
    #
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    #
    co
    #
    chash
    cfv
    c1
    wceq
    #
    vw
    cv
    #
    @2
    wcel
    #
    vw
    weu
    #
    @0
    @2
    c0
    wne
    @5
    vt
    cv
    #
    @2
    wcel
    #
    wa
    #
    @4
    @7
    wceq
    #
    wi
    #
    vt
    wal
    vw
    wal
    @6
    cA
    cB
    cG
    cV
    frgr2wwlkeu.v
    frgr2wwlkn0
    @0
    @11
    vw
    vt
    @9
    @4
    cA
    vd
    cv
    #
    cB
    cs3
    #
    wceq
    #
    @13
    @2
    wcel
    #
    wa
    #
    vd
    cV
    wrex
    #
    @7
    cA
    vc
    cv
    #
    cB
    cs3
    #
    wceq
    #
    @19
    @2
    wcel
    #
    wa
    #
    vc
    cV
    wrex
    #
    wa
    #
    @0
    @10
    @5
    @17
    @8
    @23
    cA
    cB
    cG
    cV
    @4
    vd
    frgr2wwlkeu.v
    elwwlks2ons3
    cA
    cB
    cG
    cV
    @7
    vc
    frgr2wwlkeu.v
    elwwlks2ons3
    anbi12i
    @0
    cA
    vx
    cv
    #
    cB
    cs3
    #
    @2
    wcel
    #
    vx
    cV
    wreu
    #
    @24
    @10
    wi
    cA
    cB
    cG
    cV
    vx
    frgr2wwlkeu.v
    frgr2wwlkeu
    @28
    @17
    @23
    @10
    @28
    @16
    @23
    @10
    wi
    vd
    cV
    @28
    @12
    cV
    wcel
    #
    wa
    #
    @23
    @16
    @10
    @30
    @22
    @16
    @10
    wi
    #
    vc
    cV
    @28
    @29
    @18
    cV
    wcel
    #
    @22
    @31
    wi
    #
    @28
    @27
    vx
    cV
    wrex
    @27
    cA
    vy
    cv
    #
    cB
    cs3
    #
    @2
    wcel
    #
    wa
    #
    @25
    @34
    wceq
    #
    wi
    #
    vy
    cV
    wral
    vx
    cV
    wral
    #
    @29
    @32
    wa
    #
    @33
    wi
    @27
    @36
    vx
    vy
    cV
    @38
    @26
    @35
    @2
    cA
    @25
    cB
    @34
    s3eq2
    eleq1d
    reu4
    @41
    @40
    @33
    @41
    @40
    wa
    @15
    @21
    wa
    #
    @12
    @18
    wceq
    #
    wi
    #
    @33
    @39
    @44
    @15
    @36
    wa
    #
    @12
    @34
    wceq
    #
    wi
    vx
    vy
    @12
    @18
    cV
    cV
    @25
    @12
    wceq
    #
    @37
    @45
    @38
    @46
    @47
    @27
    @15
    @36
    @47
    @26
    @13
    @2
    cA
    @25
    cB
    @12
    s3eq2
    eleq1d
    anbi1d
    vx
    vd
    vy
    equequ1
    imbi12d
    @34
    @18
    wceq
    #
    @45
    @42
    @46
    @43
    @48
    @36
    @21
    @15
    @48
    @35
    @19
    @2
    cA
    @34
    cB
    @18
    s3eq2
    eleq1d
    anbi2d
    vy
    vc
    vd
    equequ2
    imbi12d
    rspc2va
    @16
    @22
    @44
    @10
    @14
    @15
    @22
    @44
    @10
    wi
    #
    wi
    @22
    @15
    @14
    @49
    @20
    @21
    @15
    @14
    @49
    wi
    #
    wi
    @15
    @21
    @20
    @50
    @15
    @21
    @20
    @14
    @49
    @42
    @44
    @20
    @14
    wa
    #
    @10
    @42
    @44
    @51
    @10
    wi
    #
    @42
    @44
    wa
    @43
    @52
    @42
    @43
    pm3.35
    @43
    @51
    @10
    @43
    @51
    wa
    #
    vt
    vw
    @53
    @7
    @4
    wceq
    #
    @19
    @13
    wceq
    #
    @43
    @55
    @51
    @55
    vc
    vd
    cA
    @18
    cB
    @12
    s3eq2
    equcoms
    adantr
    @51
    @54
    @55
    wb
    @43
    @7
    @19
    @4
    @13
    eqeq12
    adantl
    mpbird
    equcomd
    ex
    syl
    ex
    com23
    exp4b
    com13
    imp
    com13
    imp
    com13
    syl
    expcom
    simplbiim
    impl
    rexlimdva
    com23
    rexlimdva
    impd
    syl
    syl5bi
    alrimivv
    vw
    vt
    @2
    eqeuel
    syl2anc
    @2
    cvv
    wcel
    @3
    @6
    wb
    @0
    cA
    cB
    @1
    ovex
    @2
    cvv
    vw
    euhash1
    mp1i
    mpbird
end
