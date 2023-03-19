include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "cfv.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "coms.mm"
include "cvv.mm"
include "wceq.mm"
include "simp2.mm"
include "simp1.mm"
include "fex.mm"
include "syl2anc.mm"
include "omsval.mm"
include "syl.mm"
include "simpr.mm"
include "sseq1d.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "simp3.mm"
include "fdm.mm"
include "3ad2ant2.mm"
include "unieqd.mm"
include "sseqtr4d.mm"
include "wb.mm"
include "elex.mm"
include "uniexb.mm"
include "biimpi.mm"
include "3syl.mm"
include "ssexg.mm"
include "elpwg.mm"
include "mpbird.mm"
include "cxr.mm"
include "wor.mm"
include "xrltso.mm"
include "wi.mm"
include "iccssxr.mm"
include "soss.mm"
include "ax-mp.mm"
include "mp1i.mm"
include "infexd.mm"
include "fvmptd.mm"

theorem omsfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cV: class V
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint A a
  disjoint A s
  disjoint A t
  disjoint A w
  disjoint Q a
  disjoint V a
  assert |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) /\ A C_ U. Q ) -> ( ( toOMeas ` R ) ` A ) = inf ( ran ( x e. { z e. ~P dom R | ( A C_ U. z /\ z ~<_ _om ) } |-> sum* y e. x ( R ` y ) ) , ( 0 [,] +oo ) , < ) )

  proof
    cQ
    cV
    wcel
    #
    cQ
    cc0
    cpnf
    cicc
    co
    #
    cR
    wf
    #
    cA
    cQ
    cuni
    #
    wss
    #
    w3a
    #
    va
    cA
    vx
    va
    cv
    #
    vz
    cv
    #
    cuni
    #
    wss
    #
    @7
    com
    cdom
    wbr
    #
    wa
    #
    vz
    cR
    cdm
    #
    cpw
    #
    crab
    #
    vx
    cv
    vy
    cv
    cR
    cfv
    vy
    cesum
    #
    cmpt
    #
    crn
    #
    @1
    clt
    cinf
    #
    vx
    cA
    @8
    wss
    #
    @10
    wa
    #
    vz
    @13
    crab
    #
    @15
    cmpt
    #
    crn
    #
    @1
    clt
    cinf
    @12
    cuni
    #
    cpw
    #
    cR
    coms
    cfv
    #
    cvv
    @5
    cR
    cvv
    wcel
    #
    @26
    va
    @25
    @18
    cmpt
    wceq
    @5
    @2
    @0
    @27
    @0
    @2
    @4
    simp2
    @0
    @2
    @4
    simp1
    #
    cQ
    @1
    cV
    cR
    fex
    syl2anc
    vx
    vy
    vz
    cR
    va
    omsval
    syl
    @5
    @6
    cA
    wceq
    #
    wa
    #
    @1
    @17
    @23
    clt
    @30
    @16
    @22
    @30
    vx
    @14
    @21
    @15
    @30
    @11
    @20
    vz
    @13
    @30
    @9
    @19
    @10
    @30
    @6
    cA
    @8
    @5
    @29
    simpr
    sseq1d
    anbi1d
    rabbidv
    mpteq1d
    rneqd
    infeq1d
    @5
    cA
    @25
    wcel
    #
    cA
    @24
    wss
    #
    @5
    cA
    @3
    @24
    @0
    @2
    @4
    simp3
    #
    @5
    @12
    cQ
    @2
    @0
    @12
    cQ
    wceq
    @4
    cQ
    @1
    cR
    fdm
    3ad2ant2
    unieqd
    sseqtr4d
    @5
    cA
    cvv
    wcel
    #
    @31
    @32
    wb
    @5
    @4
    @3
    cvv
    wcel
    #
    @34
    @33
    @5
    @0
    cQ
    cvv
    wcel
    #
    @35
    @28
    cQ
    cV
    elex
    @36
    @35
    cQ
    uniexb
    biimpi
    3syl
    cA
    @3
    cvv
    ssexg
    syl2anc
    cA
    @24
    cvv
    elpwg
    syl
    mpbird
    @5
    @1
    @23
    clt
    cxr
    clt
    wor
    #
    @1
    clt
    wor
    #
    @5
    xrltso
    @1
    cxr
    wss
    @37
    @38
    wi
    cc0
    cpnf
    iccssxr
    @1
    cxr
    clt
    soss
    ax-mp
    mp1i
    infexd
    fvmptd
end
