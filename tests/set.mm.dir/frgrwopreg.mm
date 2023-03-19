include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cfrgr.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c0.mm"
include "wo.mm"
include "wi.mm"
include "frgrwopreglem1.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3o.mm"
include "hashv01gt1.mm"
include "hasheq0.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "olc.mm"
include "olcd.mm"
include "2a1d.mm"
include "orc.mm"
include "orcd.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "cedg.mm"
include "wrex.mm"
include "eqid.mm"
include "frgrwopreglem5.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "wnel.mm"
include "simplll.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "rabidim1.mm"
include "adantl.mm"
include "simprl.mm"
include "cdif.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "4cyclusnfrgr.mm"
include "syl133anc.mm"
include "exp4b.mm"
include "3impd.mm"
include "wn.mm"
include "df-nel.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "syl6.mm"
include "rexlimdvva.mm"
include "com23.mm"
include "mpcom.mm"
include "3ad2ant1.mm"
include "mpd.mm"
include "3exp.mm"
include "com3l.mm"
include "3jaoi.mm"
include "com12.mm"
include "syl6bi.mm"
include "imp.mm"
include "ax-mp.mm"

theorem frgrwopreg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )

  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint B x
  disjoint X x
  disjoint Y x
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint a b
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint B y
  disjoint a x
  disjoint b x
  disjoint x y
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint V y
  assert |- ( G e. FriendGraph -> ( ( ( # ` A ) = 1 \/ A = (/) ) \/ ( ( # ` B ) = 1 \/ B = (/) ) ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cG
    cfrgr
    wcel
    #
    cA
    chash
    cfv
    #
    c1
    wceq
    #
    cA
    c0
    wceq
    #
    wo
    #
    cB
    chash
    cfv
    #
    c1
    wceq
    #
    cB
    c0
    wceq
    #
    wo
    #
    wo
    #
    wi
    #
    vx
    cA
    cB
    cD
    cG
    cK
    cV
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreglem1
    @0
    @1
    @12
    @0
    @3
    cc0
    wceq
    #
    @4
    c1
    @3
    clt
    wbr
    #
    w3o
    #
    @1
    @12
    wi
    #
    cA
    cvv
    hashv01gt1
    @0
    @15
    @5
    @4
    @14
    w3o
    #
    @16
    @0
    @13
    @5
    @4
    @4
    @14
    @14
    cA
    cvv
    hasheq0
    @0
    @4
    biidd
    @0
    @14
    biidd
    3orbi123d
    @1
    @17
    @12
    @1
    @7
    cc0
    wceq
    #
    @8
    c1
    @7
    clt
    wbr
    #
    w3o
    #
    @17
    @12
    wi
    #
    cB
    cvv
    hashv01gt1
    @1
    @20
    @9
    @8
    @19
    w3o
    @21
    @1
    @18
    @9
    @8
    @8
    @19
    @19
    cB
    cvv
    hasheq0
    @1
    @8
    biidd
    @1
    @19
    biidd
    3orbi123d
    @9
    @21
    @8
    @19
    @9
    @11
    @17
    @2
    @9
    @10
    @6
    @9
    @8
    olc
    olcd
    2a1d
    @8
    @11
    @17
    @2
    @8
    @10
    @6
    @8
    @9
    orc
    olcd
    2a1d
    @17
    @19
    @12
    @5
    @19
    @12
    wi
    @4
    @14
    @5
    @11
    @19
    @2
    @5
    @6
    @10
    @5
    @4
    olc
    orcd
    2a1d
    @4
    @11
    @19
    @2
    @4
    @6
    @10
    @4
    @5
    orc
    orcd
    2a1d
    @2
    @14
    @19
    @11
    @2
    @14
    @19
    @11
    @2
    @14
    @19
    w3a
    va
    cv
    #
    vx
    cv
    #
    wne
    #
    vb
    cv
    #
    vy
    cv
    #
    wne
    #
    wa
    #
    @22
    @25
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @25
    @23
    cpr
    @29
    wcel
    wa
    #
    @23
    @26
    cpr
    @29
    wcel
    @26
    @22
    cpr
    @29
    wcel
    wa
    #
    w3a
    #
    vy
    cB
    wrex
    vb
    cB
    wrex
    #
    vx
    cA
    wrex
    va
    cA
    wrex
    #
    @11
    vx
    vy
    cA
    cB
    cD
    @29
    cG
    cK
    cV
    va
    vb
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    @29
    eqid
    #
    frgrwopreglem5
    @2
    @14
    @34
    @11
    wi
    #
    @19
    cG
    cusgr
    wcel
    #
    @2
    @36
    cG
    frgrusgr
    @37
    @34
    @2
    @11
    @37
    @33
    @12
    va
    vx
    cA
    cA
    @37
    @22
    cA
    wcel
    #
    @23
    cA
    wcel
    #
    wa
    #
    wa
    #
    @32
    @12
    vb
    vy
    cB
    cB
    @41
    @25
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    wa
    #
    wa
    #
    @32
    cG
    cfrgr
    wnel
    #
    @12
    @45
    @28
    @30
    @31
    @46
    @45
    @28
    @30
    @31
    @46
    @45
    @28
    wa
    @37
    @22
    cV
    wcel
    #
    @23
    cV
    wcel
    #
    @24
    @25
    cV
    wcel
    #
    @26
    cV
    wcel
    #
    @27
    @30
    @31
    wa
    @46
    wi
    @37
    @40
    @44
    @28
    simplll
    @40
    @47
    @37
    @44
    @28
    @38
    @47
    @39
    @47
    @22
    @23
    cD
    cfv
    cK
    wceq
    #
    vx
    cV
    crab
    #
    cA
    @51
    vx
    @22
    cV
    elrabi
    frgrwopreg.a
    eleq2s
    adantr
    ad3antlr
    @40
    @48
    @37
    @44
    @28
    @39
    @48
    @38
    @48
    @23
    @52
    cA
    @51
    vx
    cV
    rabidim1
    frgrwopreg.a
    eleq2s
    adantl
    ad3antlr
    @45
    @24
    @27
    simprl
    @44
    @49
    @41
    @28
    @42
    @49
    @43
    @49
    @25
    cV
    cA
    cdif
    #
    cB
    @25
    cV
    cA
    eldifi
    frgrwopreg.b
    eleq2s
    adantr
    ad2antlr
    @44
    @50
    @41
    @28
    @43
    @50
    @42
    @50
    @26
    @53
    cB
    @26
    cV
    cA
    eldifi
    frgrwopreg.b
    eleq2s
    adantl
    ad2antlr
    @45
    @24
    @27
    simprr
    @22
    @25
    @23
    @26
    @29
    cG
    cV
    frgrwopreg.v
    @35
    4cyclusnfrgr
    syl133anc
    exp4b
    3impd
    @46
    @2
    wn
    @12
    cG
    cfrgr
    df-nel
    @2
    @11
    pm2.21
    sylbi
    syl6
    rexlimdvva
    rexlimdvva
    com23
    mpcom
    3ad2ant1
    mpd
    3exp
    com3l
    3jaoi
    com12
    3jaoi
    syl6bi
    mpd
    com12
    syl6bi
    mpd
    imp
    ax-mp
end
