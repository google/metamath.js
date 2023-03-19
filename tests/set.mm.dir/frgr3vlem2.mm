include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "ctp.mm"
include "wceq.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "wb.mm"
include "weu.mm"
include "df-reu.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "eleq1.mm"
include "preq1.mm"
include "preq12d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "eu4.mm"
include "frgr3vlem1.mm"
include "3expa.mm"
include "biantrud.mm"
include "w3o.mm"
include "vex.mm"
include "eltp.mm"
include "prex.mm"
include "prss.mm"
include "usgredgne.mm"
include "adantll.mm"
include "wn.mm"
include "df-ne.mm"
include "eqid.mm"
include "pm2.24i.mm"
include "sylbi.mm"
include "syl.mm"
include "ex.mm"
include "adantl.mm"
include "com12.mm"
include "adantr.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "ax-1.mm"
include "3jaoi.mm"
include "imp.mm"
include "exlimdv.mm"
include "wrex.mm"
include "prssi.mm"
include "3mix3d.mm"
include "rextpg.mm"
include "ad3antrrr.mm"
include "mpbird.mm"
include "df-rex.mm"
include "sylib.mm"
include "impbid.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem frgr3vlem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  assume frgr3v.v: |- V = ( Vtx ` G )
  assume frgr3v.e: |- E = ( Edg ` G )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint E x
  disjoint G x
  disjoint V x
  disjoint X x
  disjoint Y x
  disjoint Z x
  disjoint A k
  disjoint A l
  disjoint A y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B k
  disjoint B l
  disjoint B y
  disjoint C k
  disjoint C l
  disjoint C y
  disjoint E k
  disjoint E l
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y y
  disjoint Z y
  assert |- ( ( ( A e. X /\ B e. Y /\ C e. Z ) /\ ( A =/= B /\ A =/= C /\ B =/= C ) ) -> ( ( V = { A , B , C } /\ G e. USGraph ) -> ( E! x e. { A , B , C } { { x , A } , { x , B } } C_ E <-> ( { C , A } e. E /\ { C , B } e. E ) ) ) )

  proof
    cA
    cX
    wcel
    cB
    cY
    wcel
    cC
    cZ
    wcel
    w3a
    #
    cA
    cB
    wne
    cA
    cC
    wne
    cB
    cC
    wne
    w3a
    #
    wa
    #
    cV
    cA
    cB
    cC
    ctp
    #
    wceq
    #
    cG
    cusgr
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    cpr
    #
    @7
    cB
    cpr
    #
    cpr
    #
    cE
    wss
    #
    vx
    @3
    wreu
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    cC
    cB
    cpr
    #
    cE
    wcel
    wa
    #
    wb
    @12
    @7
    @3
    wcel
    #
    @11
    wa
    #
    vx
    weu
    #
    @2
    @6
    wa
    #
    @15
    @11
    vx
    @3
    df-reu
    @18
    @17
    vx
    wex
    #
    @17
    vy
    cv
    #
    @3
    wcel
    #
    @21
    cA
    cpr
    #
    @21
    cB
    cpr
    #
    cpr
    #
    cE
    wss
    #
    wa
    #
    wa
    @7
    @21
    wceq
    #
    wi
    vy
    wal
    vx
    wal
    #
    wa
    #
    @19
    @15
    @17
    @27
    vx
    vy
    @28
    @16
    @22
    @11
    @26
    @7
    @21
    @3
    eleq1
    @28
    @10
    @25
    cE
    @28
    @8
    @23
    @9
    @24
    @7
    @21
    cA
    preq1
    @7
    @21
    cB
    preq1
    preq12d
    sseq1d
    anbi12d
    eu4
    @19
    @20
    @30
    @15
    @19
    @29
    @20
    @0
    @1
    @6
    @29
    vx
    vy
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    frgr3v.v
    frgr3v.e
    frgr3vlem1
    3expa
    biantrud
    @19
    @20
    @15
    @19
    @17
    @15
    vx
    @17
    @19
    @15
    @16
    @11
    @19
    @15
    wi
    #
    @16
    @7
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    @7
    cC
    wceq
    #
    w3o
    @11
    @31
    wi
    #
    @7
    cA
    cB
    cC
    vx
    vex
    eltp
    @32
    @35
    @33
    @34
    @32
    @11
    cA
    cA
    cpr
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cE
    wss
    #
    @31
    @32
    @10
    @38
    cE
    @32
    @8
    @36
    @9
    @37
    @7
    cA
    cA
    preq1
    @7
    cA
    cB
    preq1
    preq12d
    sseq1d
    #
    @39
    @36
    cE
    wcel
    #
    @37
    cE
    wcel
    #
    wa
    @31
    @36
    @37
    cE
    cA
    cA
    prex
    cA
    cB
    prex
    prss
    @41
    @31
    @42
    @19
    @41
    @15
    @6
    @41
    @15
    wi
    @2
    @6
    @41
    @15
    @6
    @41
    wa
    cA
    cA
    wne
    #
    @15
    @5
    @41
    @43
    @4
    cE
    cG
    cA
    cA
    frgr3v.e
    usgredgne
    adantll
    @43
    cA
    cA
    wceq
    #
    wn
    @15
    cA
    cA
    df-ne
    @44
    @15
    cA
    eqid
    pm2.24i
    sylbi
    syl
    ex
    adantl
    com12
    adantr
    sylbir
    syl6bi
    @33
    @11
    cB
    cA
    cpr
    #
    cB
    cB
    cpr
    #
    cpr
    #
    cE
    wss
    #
    @31
    @33
    @10
    @47
    cE
    @33
    @8
    @45
    @9
    @46
    @7
    cB
    cA
    preq1
    @7
    cB
    cB
    preq1
    preq12d
    sseq1d
    #
    @48
    @45
    cE
    wcel
    #
    @46
    cE
    wcel
    #
    wa
    @31
    @45
    @46
    cE
    cB
    cA
    prex
    cB
    cB
    prex
    prss
    @51
    @31
    @50
    @19
    @51
    @15
    @6
    @51
    @15
    wi
    @2
    @6
    @51
    @15
    @6
    @51
    wa
    cB
    cB
    wne
    #
    @15
    @5
    @51
    @52
    @4
    cE
    cG
    cB
    cB
    frgr3v.e
    usgredgne
    adantll
    @52
    cB
    cB
    wceq
    #
    wn
    @15
    cB
    cB
    df-ne
    @53
    @15
    cB
    eqid
    pm2.24i
    sylbi
    syl
    ex
    adantl
    com12
    adantl
    sylbir
    syl6bi
    @34
    @11
    @13
    @14
    cpr
    #
    cE
    wss
    #
    @31
    @34
    @10
    @54
    cE
    @34
    @8
    @13
    @9
    @14
    @7
    cC
    cA
    preq1
    @7
    cC
    cB
    preq1
    preq12d
    sseq1d
    #
    @55
    @15
    @31
    @13
    @14
    cE
    cC
    cA
    prex
    cC
    cB
    prex
    prss
    @15
    @19
    ax-1
    sylbir
    syl6bi
    3jaoi
    sylbi
    imp
    com12
    exlimdv
    @19
    @15
    @20
    @19
    @15
    wa
    #
    @11
    vx
    @3
    wrex
    #
    @20
    @57
    @58
    @39
    @48
    @55
    w3o
    #
    @57
    @55
    @39
    @48
    @15
    @55
    @19
    @13
    @14
    cE
    prssi
    adantl
    3mix3d
    @0
    @58
    @59
    wb
    @1
    @6
    @15
    @11
    @39
    @48
    @55
    vx
    cA
    cB
    cC
    cX
    cY
    cZ
    @40
    @49
    @56
    rextpg
    ad3antrrr
    mpbird
    @11
    vx
    @3
    df-rex
    sylib
    ex
    impbid
    bitr3d
    syl5bb
    syl5bb
    ex
end
