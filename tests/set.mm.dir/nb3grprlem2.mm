include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "ctp.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "w3o.mm"
include "wcel.mm"
include "w3a.mm"
include "wb.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "rextpg.mm"
include "syl.mm"
include "cusgr.mm"
include "wa.mm"
include "jca.mm"
include "simpl.mm"
include "difeq1.mm"
include "adantr.mm"
include "rexeqdv.mm"
include "wo.mm"
include "preq2.mm"
include "rexprg.mm"
include "3adant1.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant3.mm"
include "3orbi123d.mm"
include "wne.mm"
include "tprot.mm"
include "a1i.mm"
include "difeq1d.mm"
include "necom.mm"
include "diftpsn3.mm"
include "syl2anb.mm"
include "eqtrd.mm"
include "eqcomi.mm"
include "anbi1i.mm"
include "biimpi.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "orbi2i.mm"
include "oridm.mm"
include "bitr2i.mm"
include "wn.mm"
include "wnel.mm"
include "nbgrnself2.mm"
include "wi.mm"
include "df-nel.mm"
include "prid2g.mm"
include "3ad2ant1.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "con3rr3.mm"
include "sylbi.mm"
include "mpsyl.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "orbi12d.mm"
include "prid1g.mm"
include "con3dimp.mm"
include "expcom.mm"
include "ioran.mm"
include "sylibr.mm"
include "3bior1fd.mm"
include "3bitrd.mm"
include "3bitr4rd.mm"

theorem nb3grprlem2
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume nb3grpr.v: |- V = ( Vtx ` G )
  assume nb3grpr.e: |- E = ( Edg ` G )
  assume nb3grpr.g: |- ( ph -> G e. USGraph )
  assume nb3grpr.t: |- ( ph -> V = { A , B , C } )
  assume nb3grpr.s: |- ( ph -> ( A e. X /\ B e. Y /\ C e. Z ) )
  assume nb3grpr.n: |- ( ph -> ( A =/= B /\ A =/= C /\ B =/= C ) )

  disjoint A v
  disjoint B v
  disjoint C v
  disjoint E v
  disjoint G v
  disjoint V v
  disjoint ph v
  disjoint A w
  disjoint v w
  disjoint B w
  disjoint C w
  disjoint G w
  disjoint V w
  assert |- ( ph -> ( ( G NeighbVtx A ) = { B , C } <-> E. v e. V E. w e. ( V \ { v } ) ( G NeighbVtx A ) = { v , w } ) )

  proof
    wph
    cG
    cA
    cnbgr
    co
    #
    vv
    cv
    #
    vw
    cv
    #
    cpr
    #
    wceq
    #
    vw
    cA
    cB
    cC
    ctp
    #
    @1
    csn
    #
    cdif
    #
    wrex
    #
    vv
    @5
    wrex
    #
    @0
    cA
    @2
    cpr
    #
    wceq
    #
    vw
    @5
    cA
    csn
    #
    cdif
    #
    wrex
    #
    @0
    cB
    @2
    cpr
    #
    wceq
    #
    vw
    @5
    cB
    csn
    #
    cdif
    #
    wrex
    #
    @0
    cC
    @2
    cpr
    #
    wceq
    #
    vw
    @5
    cC
    csn
    #
    cdif
    #
    wrex
    #
    w3o
    #
    @4
    vw
    cV
    @6
    cdif
    #
    wrex
    #
    vv
    cV
    wrex
    #
    @0
    cB
    cC
    cpr
    #
    wceq
    #
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    @9
    @25
    wb
    nb3grpr.s
    @8
    @14
    @19
    @24
    vv
    cA
    cB
    cC
    cX
    cY
    cZ
    @1
    cA
    wceq
    #
    @4
    @11
    vw
    @7
    @13
    @35
    @6
    @12
    @5
    @1
    cA
    sneq
    difeq2d
    @35
    @3
    @10
    @0
    @1
    cA
    @2
    preq1
    eqeq2d
    rexeqbidv
    @1
    cB
    wceq
    #
    @4
    @16
    vw
    @7
    @18
    @36
    @6
    @17
    @5
    @1
    cB
    sneq
    difeq2d
    @36
    @3
    @15
    @0
    @1
    cB
    @2
    preq1
    eqeq2d
    rexeqbidv
    @1
    cC
    wceq
    #
    @4
    @21
    vw
    @7
    @23
    @37
    @6
    @22
    @5
    @1
    cC
    sneq
    difeq2d
    @37
    @3
    @20
    @0
    @1
    cC
    @2
    preq1
    eqeq2d
    rexeqbidv
    rextpg
    syl
    wph
    cV
    @5
    wceq
    #
    cG
    cusgr
    wcel
    #
    wa
    #
    @28
    @9
    wb
    wph
    @38
    @39
    nb3grpr.t
    nb3grpr.g
    jca
    @40
    @27
    @8
    vv
    cV
    @5
    @38
    @39
    simpl
    @40
    @4
    vw
    @26
    @7
    @38
    @26
    @7
    wceq
    @39
    cV
    @5
    @6
    difeq1
    adantr
    rexeqdv
    rexeqbidv
    syl
    wph
    @11
    vw
    @29
    wrex
    #
    @16
    vw
    cC
    cA
    cpr
    #
    wrex
    #
    @21
    vw
    cA
    cB
    cpr
    #
    wrex
    #
    w3o
    #
    @0
    @44
    wceq
    #
    @0
    cA
    cC
    cpr
    #
    wceq
    #
    wo
    #
    @30
    @0
    cB
    cA
    cpr
    #
    wceq
    #
    wo
    #
    @0
    @42
    wceq
    #
    @0
    cC
    cB
    cpr
    #
    wceq
    #
    wo
    #
    w3o
    #
    @25
    @30
    wph
    @34
    @46
    @58
    wb
    nb3grpr.s
    @34
    @41
    @50
    @43
    @53
    @45
    @57
    @32
    @33
    @41
    @50
    wb
    @31
    @11
    @47
    @49
    vw
    cB
    cC
    cY
    cZ
    @2
    cB
    wceq
    #
    @10
    @44
    @0
    @2
    cB
    cA
    preq2
    eqeq2d
    @2
    cC
    wceq
    #
    @10
    @48
    @0
    @2
    cC
    cA
    preq2
    eqeq2d
    rexprg
    3adant1
    @31
    @33
    @43
    @53
    wb
    #
    @32
    @33
    @31
    @61
    @16
    @30
    @52
    vw
    cC
    cA
    cZ
    cX
    @60
    @15
    @29
    @0
    @2
    cC
    cB
    preq2
    eqeq2d
    @2
    cA
    wceq
    #
    @15
    @51
    @0
    @2
    cA
    cB
    preq2
    eqeq2d
    rexprg
    ancoms
    3adant2
    @31
    @32
    @45
    @57
    wb
    @33
    @21
    @54
    @56
    vw
    cA
    cB
    cX
    cY
    @62
    @20
    @42
    @0
    @2
    cA
    cC
    preq2
    eqeq2d
    @59
    @20
    @55
    @0
    @2
    cB
    cC
    preq2
    eqeq2d
    rexprg
    3adant3
    3orbi123d
    syl
    wph
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    @25
    @46
    wb
    nb3grpr.n
    @66
    @14
    @41
    @19
    @43
    @24
    @45
    @66
    @11
    vw
    @13
    @29
    @66
    @13
    cB
    cC
    cA
    ctp
    #
    @12
    cdif
    #
    @29
    @66
    @5
    @67
    @12
    @5
    @67
    wceq
    @66
    cA
    cB
    cC
    tprot
    a1i
    difeq1d
    @63
    @64
    @68
    @29
    wceq
    #
    @65
    @63
    cB
    cA
    wne
    cC
    cA
    wne
    @69
    @64
    cA
    cB
    necom
    cA
    cC
    necom
    cB
    cC
    cA
    diftpsn3
    syl2anb
    3adant3
    eqtrd
    rexeqdv
    @66
    @16
    vw
    @18
    @42
    @66
    @18
    cC
    cA
    cB
    ctp
    #
    @17
    cdif
    #
    @42
    @66
    @5
    @70
    @17
    @5
    @70
    wceq
    @66
    @70
    @5
    cC
    cA
    cB
    tprot
    eqcomi
    a1i
    difeq1d
    @63
    @65
    @71
    @42
    wceq
    #
    @64
    @63
    @65
    wa
    cC
    cB
    wne
    #
    @63
    wa
    #
    @72
    @65
    @63
    @74
    @65
    @63
    wa
    @74
    @65
    @73
    @63
    cB
    cC
    necom
    anbi1i
    biimpi
    ancoms
    cC
    cA
    cB
    diftpsn3
    syl
    3adant2
    eqtrd
    rexeqdv
    @66
    @21
    vw
    @23
    @44
    @64
    @65
    @23
    @44
    wceq
    @63
    cA
    cB
    cC
    diftpsn3
    3adant1
    rexeqdv
    3orbi123d
    syl
    wph
    @30
    @30
    @56
    wo
    #
    @53
    @57
    wo
    @58
    @30
    @75
    wb
    wph
    @75
    @30
    @30
    wo
    @30
    @56
    @30
    @30
    @55
    @29
    @0
    cC
    cB
    prcom
    eqeq2i
    orbi2i
    @30
    oridm
    bitr2i
    a1i
    wph
    @30
    @53
    @56
    @57
    wph
    @52
    wn
    #
    @30
    @53
    wb
    cA
    @0
    wnel
    #
    wph
    @34
    @76
    cG
    cA
    nbgrnself2
    #
    nb3grpr.s
    @77
    cA
    @0
    wcel
    #
    wn
    #
    @34
    @76
    wi
    cA
    @0
    df-nel
    #
    @34
    @52
    @79
    @34
    @79
    @52
    cA
    @51
    wcel
    #
    @31
    @32
    @82
    @33
    cB
    cA
    cX
    prid2g
    3ad2ant1
    @0
    @51
    cA
    eleq2
    syl5ibrcom
    con3rr3
    sylbi
    mpsyl
    @76
    @30
    @52
    @30
    wo
    @53
    @52
    @30
    biorf
    @52
    @30
    orcom
    syl6bb
    syl
    wph
    @54
    wn
    #
    @56
    @57
    wb
    @77
    wph
    @34
    @83
    @78
    nb3grpr.s
    @77
    @80
    @34
    @83
    wi
    @81
    @34
    @54
    @79
    @34
    @79
    @54
    cA
    @42
    wcel
    #
    @31
    @32
    @84
    @33
    cC
    cA
    cX
    prid2g
    3ad2ant1
    @0
    @42
    cA
    eleq2
    syl5ibrcom
    con3rr3
    sylbi
    mpsyl
    @54
    @56
    biorf
    syl
    orbi12d
    wph
    @57
    @53
    @50
    wph
    @47
    wn
    #
    @49
    wn
    #
    wa
    #
    @50
    wn
    @77
    wph
    @34
    @87
    @78
    nb3grpr.s
    @77
    @80
    @34
    @87
    wi
    @81
    @34
    @80
    @87
    @34
    @80
    wa
    @85
    @86
    @34
    @47
    @79
    @34
    @79
    @47
    cA
    @44
    wcel
    #
    @31
    @32
    @88
    @33
    cA
    cB
    cX
    prid1g
    3ad2ant1
    @0
    @44
    cA
    eleq2
    syl5ibrcom
    con3dimp
    @34
    @49
    @79
    @34
    @79
    @49
    cA
    @48
    wcel
    #
    @31
    @32
    @89
    @33
    cA
    cC
    cX
    prid1g
    3ad2ant1
    @0
    @48
    cA
    eleq2
    syl5ibrcom
    con3dimp
    jca
    expcom
    sylbi
    mpsyl
    @47
    @49
    ioran
    sylibr
    3bior1fd
    3bitrd
    3bitr4rd
    3bitr4rd
end
