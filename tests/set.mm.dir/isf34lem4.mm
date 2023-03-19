include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cuni.mm"
include "cfv.mm"
include "cv.mm"
include "cdif.mm"
include "crab.mm"
include "cint.mm"
include "cima.mm"
include "wceq.mm"
include "sspwuni.mm"
include "isf34lem1.mm"
include "sylan2b.mm"
include "adantrr.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "simplrr.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eldifd.mm"
include "elunii.mm"
include "syl2anc.mm"
include "ex.mm"
include "mt3d.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wex.mm"
include "n0.mm"
include "sselda.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "eldifi.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "impr.mm"
include "eluni.mm"
include "wrex.mm"
include "adantlrr.mm"
include "adantrl.mm"
include "elndif.mm"
include "ad2antrl.mm"
include "jca.mm"
include "annim.mm"
include "notbid.mm"
include "rspcev.mm"
include "rexnal.mm"
include "con2d.mm"
include "jcad.mm"
include "impbid.mm"
include "eldif.mm"
include "vex.mm"
include "elintrab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqtrd.mm"
include "compss.mm"
include "inteqi.mm"
include "syl6eqr.mm"

theorem isf34lem4
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
  disjoint V x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( ( A e. V /\ ( X C_ ~P A /\ X =/= (/) ) ) -> ( F ` U. X ) = |^| ( F " X ) )

  proof
    cA
    cV
    wcel
    #
    cX
    cA
    cpw
    #
    wss
    #
    cX
    c0
    wne
    #
    wa
    #
    wa
    #
    cX
    cuni
    #
    cF
    cfv
    #
    cA
    va
    cv
    #
    cdif
    #
    cX
    wcel
    #
    va
    @1
    crab
    #
    cint
    #
    cF
    cX
    cima
    #
    cint
    @5
    @7
    cA
    @6
    cdif
    #
    @12
    @0
    @2
    @7
    @14
    wceq
    #
    @3
    @2
    @0
    @6
    cA
    wss
    @15
    cX
    cA
    sspwuni
    vx
    cA
    cF
    cV
    @6
    compss.a
    isf34lem1
    sylan2b
    adantrr
    @5
    vb
    @14
    @12
    @5
    vb
    cv
    #
    cA
    wcel
    #
    @16
    @6
    wcel
    #
    wn
    #
    wa
    #
    @10
    @16
    @8
    wcel
    #
    wi
    #
    va
    @1
    wral
    #
    @16
    @14
    wcel
    @16
    @12
    wcel
    @5
    @20
    @23
    @5
    @20
    @23
    @5
    @20
    wa
    #
    @22
    va
    @1
    @24
    @8
    @1
    wcel
    #
    @10
    @21
    @24
    @25
    @10
    wa
    #
    wa
    #
    @21
    @18
    @5
    @17
    @19
    @26
    simplrr
    @27
    @21
    wn
    #
    @18
    @27
    @28
    wa
    #
    @16
    @9
    wcel
    @10
    @18
    @29
    @16
    cA
    @8
    @24
    @17
    @26
    @28
    @5
    @17
    @19
    simprl
    ad2antrr
    @27
    @28
    simpr
    eldifd
    @24
    @25
    @10
    @28
    simplrr
    @16
    @9
    cX
    elunii
    syl2anc
    ex
    mt3d
    expr
    ralrimiva
    ex
    @5
    @23
    @17
    @19
    @0
    @2
    @3
    @23
    @17
    wi
    #
    @3
    vc
    cv
    #
    cX
    wcel
    #
    vc
    wex
    @0
    @2
    wa
    #
    @30
    vc
    cX
    n0
    @33
    @32
    @30
    vc
    @33
    @32
    @30
    @33
    @32
    wa
    #
    @23
    @16
    cA
    @31
    cdif
    #
    wcel
    #
    @17
    @34
    @23
    cA
    @35
    cdif
    #
    cX
    wcel
    #
    @36
    @34
    @37
    @31
    cX
    @34
    @31
    cA
    wss
    @37
    @31
    wceq
    @34
    @31
    cA
    @33
    cX
    @1
    @31
    @0
    @2
    simpr
    sselda
    elpwid
    @31
    cA
    dfss4
    sylib
    @33
    @32
    simpr
    eqeltrd
    #
    @34
    @35
    @1
    wcel
    #
    @23
    @38
    @36
    wi
    #
    wi
    @0
    @40
    @2
    @32
    @0
    @40
    @35
    cA
    wss
    cA
    @31
    difss
    @35
    cA
    cV
    elpw2g
    mpbiri
    #
    ad2antrr
    @22
    @41
    va
    @35
    @1
    @8
    @35
    wceq
    #
    @10
    @38
    @21
    @36
    @43
    @9
    @37
    cX
    @8
    @35
    cA
    difeq2
    eleq1d
    @8
    @35
    @16
    eleq2
    imbi12d
    #
    rspcv
    syl
    mpid
    @16
    cA
    @31
    eldifi
    syl6
    ex
    exlimdv
    syl5bi
    impr
    @5
    @18
    @23
    @18
    @16
    @31
    wcel
    #
    @32
    wa
    #
    vc
    wex
    @5
    @23
    wn
    #
    vc
    @16
    cX
    eluni
    @5
    @46
    @47
    vc
    @5
    @46
    @47
    @5
    @46
    wa
    #
    @22
    wn
    #
    va
    @1
    wrex
    #
    @47
    @48
    @40
    @41
    wn
    #
    @50
    @0
    @40
    @4
    @46
    @42
    ad2antrr
    @48
    @38
    @36
    wn
    #
    wa
    @51
    @48
    @38
    @52
    @5
    @32
    @38
    @45
    @0
    @2
    @32
    @38
    @3
    @39
    adantlrr
    adantrl
    @45
    @52
    @5
    @32
    @16
    @31
    cA
    elndif
    ad2antrl
    jca
    @38
    @36
    annim
    sylib
    @49
    @51
    va
    @35
    @1
    @43
    @22
    @41
    @44
    notbid
    rspcev
    syl2anc
    @22
    va
    @1
    rexnal
    sylib
    ex
    exlimdv
    syl5bi
    con2d
    jcad
    impbid
    @16
    cA
    @6
    eldif
    @10
    va
    @16
    @1
    vb
    vex
    elintrab
    3bitr4g
    eqrdv
    eqtrd
    @13
    @11
    vx
    va
    cA
    cF
    cX
    compss.a
    compss
    inteqi
    syl6eqr
end
