include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wi.mm"
include "crab.mm"
include "elovmpt3imp.mm"
include "simprl.mm"
include "cdm.mm"
include "elfvdm.mm"
include "wceq.mm"
include "simpl.mm"
include "adantr.mm"
include "simplr.mm"
include "simprr.mm"
include "ovmpt3rabdm.mm"
include "syl31anc.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "imp.mm"
include "wsbc.mm"
include "adantl.mm"
include "cmpt.mm"
include "w3a.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "ad2antll.mm"
include "cv.mm"
include "sbceq1a.mm"
include "sylan9bbr.mm"
include "nfsbc1v.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "ovmpt3rab1.mm"
include "fveq1d.mm"
include "syl.mm"
include "rabexg.mm"
include "nfrab.mm"
include "rabbidv.mm"
include "eqid.mm"
include "fvmptf.mm"
include "sylan2.mm"
include "eqtr2d.mm"
include "eleqtrrd.mm"
include "elrabi.mm"
include "jca.mm"
include "mpancom.mm"
include "exp31.mm"
include "mpcom.mm"
include "exp32.mm"
include "mpd.mm"
include "com12.mm"

theorem elovmpt3rab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cT: class T
  let cU: class U
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let cV: class V
  let cW: class W
  assume ovmpt3rab1.o: |- O = ( x e. _V , y e. _V |-> ( z e. M |-> { a e. N | ph } ) )
  assume ovmpt3rab1.m: |- ( ( x = X /\ y = Y ) -> M = K )
  assume ovmpt3rab1.n: |- ( ( x = X /\ y = Y ) -> N = L )

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint L a
  disjoint L x
  disjoint L y
  disjoint a x
  disjoint a y
  disjoint N a
  disjoint U x
  disjoint U y
  disjoint X a
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a z
  disjoint Y a
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint L z
  disjoint T z
  disjoint U z
  disjoint A a
  disjoint Z a
  disjoint Z z
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint V z
  disjoint W z
  assert |- ( ( K e. U /\ L e. T ) -> ( A e. ( ( X O Y ) ` Z ) -> ( ( X e. _V /\ Y e. _V ) /\ ( Z e. K /\ A e. L ) ) ) )

  proof
    cA
    cZ
    cX
    cY
    cO
    co
    #
    cfv
    #
    wcel
    #
    cK
    cU
    wcel
    #
    cL
    cT
    wcel
    #
    wa
    #
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    cZ
    cK
    wcel
    #
    cA
    cL
    wcel
    #
    wa
    #
    wa
    #
    @2
    @8
    @5
    @12
    wi
    vx
    vy
    vz
    cA
    wph
    va
    cN
    crab
    cM
    cO
    cX
    cY
    cZ
    ovmpt3rab1.o
    elovmpt3imp
    @2
    @8
    @5
    @12
    @2
    @8
    @5
    wa
    #
    wa
    @8
    @11
    @2
    @8
    @5
    simprl
    @2
    @13
    @11
    cZ
    @0
    cdm
    #
    wcel
    #
    @2
    @13
    @11
    wi
    cA
    cZ
    @0
    elfvdm
    @15
    @2
    @13
    @11
    @9
    @15
    @2
    wa
    #
    @13
    wa
    #
    @11
    @16
    @13
    @9
    @15
    @13
    @9
    wi
    @2
    @13
    @15
    @9
    @13
    @14
    cK
    cZ
    @13
    @6
    @7
    @3
    @4
    @14
    cK
    wceq
    @8
    @6
    @5
    @6
    @7
    simpl
    adantr
    @6
    @7
    @5
    simplr
    @8
    @3
    @4
    simprl
    @8
    @3
    @4
    simprr
    wph
    vx
    vy
    vz
    cT
    cU
    cK
    cL
    cM
    cN
    cO
    cvv
    cvv
    cX
    cY
    va
    ovmpt3rab1.o
    ovmpt3rab1.m
    ovmpt3rab1.n
    ovmpt3rabdm
    syl31anc
    eleq2d
    biimpcd
    adantr
    imp
    @9
    @17
    wa
    #
    @9
    @10
    @9
    @17
    simpl
    @18
    cA
    wph
    vy
    cY
    wsbc
    #
    vx
    cX
    wsbc
    #
    vz
    cZ
    wsbc
    #
    va
    cL
    crab
    #
    wcel
    @10
    @18
    cA
    @1
    @22
    @17
    @2
    @9
    @15
    @2
    @13
    simplr
    adantl
    @18
    @1
    cZ
    vz
    cK
    @20
    va
    cL
    crab
    #
    cmpt
    #
    cfv
    #
    @22
    @18
    @6
    @7
    @3
    w3a
    #
    @1
    @25
    wceq
    @13
    @26
    @9
    @16
    @13
    @8
    @3
    wa
    @26
    @5
    @3
    @8
    @3
    @4
    simpl
    anim2i
    @6
    @7
    @3
    df-3an
    sylibr
    ad2antll
    @26
    cZ
    @0
    @24
    wph
    @20
    vx
    vy
    vz
    cU
    cK
    cL
    cM
    cN
    cO
    cvv
    cvv
    cX
    cY
    va
    ovmpt3rab1.o
    ovmpt3rab1.m
    ovmpt3rab1.n
    vy
    cv
    cY
    wceq
    wph
    @19
    vx
    cv
    cX
    wceq
    @20
    wph
    vy
    cY
    sbceq1a
    @19
    vx
    cX
    sbceq1a
    sylan9bbr
    @19
    vx
    cX
    nfsbc1v
    @19
    vy
    vx
    cX
    vy
    cX
    nfcv
    wph
    vy
    cY
    nfsbc1v
    nfsbc
    ovmpt3rab1
    fveq1d
    syl
    @17
    @9
    @22
    cvv
    wcel
    #
    @25
    @22
    wceq
    @5
    @27
    @16
    @8
    @4
    @27
    @3
    @21
    va
    cL
    cT
    rabexg
    adantl
    ad2antll
    vz
    cZ
    @23
    @22
    cK
    @24
    cvv
    vz
    cZ
    nfcv
    @21
    vz
    va
    cL
    @20
    vz
    cZ
    nfsbc1v
    vz
    cL
    nfcv
    nfrab
    vz
    cv
    cZ
    wceq
    @20
    @21
    va
    cL
    @20
    vz
    cZ
    sbceq1a
    rabbidv
    @24
    eqid
    fvmptf
    sylan2
    eqtr2d
    eleqtrrd
    @21
    va
    cA
    cL
    elrabi
    syl
    jca
    mpancom
    exp31
    mpcom
    imp
    jca
    exp32
    mpd
    com12
end
