include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cesum.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "vex.mm"
include "simp2.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "wceq.mm"
include "fdm.mm"
include "pweqd.mm"
include "syl.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "elpwi.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "sylancr.mm"
include "eqid.mm"
include "rnmptss.mm"

theorem omscl
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
  assert |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) /\ A e. ~P U. dom R ) -> ran ( x e. { z e. ~P dom R | ( A C_ U. z /\ z ~<_ _om ) } |-> sum* y e. x ( R ` y ) ) C_ ( 0 [,] +oo ) )

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
    cR
    cdm
    #
    cuni
    cpw
    wcel
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cfv
    #
    vy
    cesum
    #
    @1
    wcel
    #
    vx
    cA
    vz
    cv
    #
    cuni
    wss
    @11
    com
    cdom
    wbr
    wa
    #
    vz
    @3
    cpw
    #
    crab
    #
    wral
    vx
    @14
    @9
    cmpt
    #
    crn
    @1
    wss
    @5
    @10
    vx
    @14
    @5
    @6
    @14
    wcel
    #
    wa
    #
    @6
    cvv
    wcel
    @8
    @1
    wcel
    #
    vy
    @6
    wral
    @10
    vx
    vex
    @17
    @18
    vy
    @6
    @17
    @7
    @6
    wcel
    #
    wa
    cQ
    @1
    @7
    cR
    @5
    @2
    @16
    @19
    @0
    @2
    @4
    simp2
    #
    ad2antrr
    @17
    @6
    cQ
    @7
    @17
    @6
    cQ
    cpw
    #
    wcel
    @6
    cQ
    wss
    @17
    @6
    @13
    @21
    @17
    @14
    @13
    @6
    @12
    vz
    @13
    ssrab2
    @5
    @16
    simpr
    sseldi
    @5
    @13
    @21
    wceq
    #
    @16
    @5
    @2
    @22
    @20
    @2
    @3
    cQ
    cQ
    @1
    cR
    fdm
    pweqd
    syl
    adantr
    eleqtrd
    @6
    cQ
    elpwi
    syl
    sselda
    ffvelrnd
    ralrimiva
    @6
    @8
    vy
    cvv
    vy
    @6
    nfcv
    esumcl
    sylancr
    ralrimiva
    vx
    @14
    @9
    @1
    @15
    @15
    eqid
    rnmptss
    syl
end
