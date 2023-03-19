include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "weq.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "3anbi13d.mm"
include "exbidv.mm"
include "fneq2.mm"
include "sseq1.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "predeq3.mm"
include "sseq1d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "raleq.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "3anbi123d.mm"
include "cbvexv.mm"
include "cbvabv.mm"
include "eqtri.mm"

theorem wfrlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  assume wfrlem1.1: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( F ` ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A f
  disjoint A g
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f g
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R f
  disjoint R g
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- B = { g | E. z ( g Fn z /\ ( z C_ A /\ A. w e. z Pred ( R , A , w ) C_ z ) /\ A. w e. z ( g ` w ) = ( F ` ( g |` Pred ( R , A , w ) ) ) ) }

  proof
    cB
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    @1
    cA
    wss
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @1
    wss
    #
    vy
    @1
    wral
    #
    wa
    #
    @4
    @0
    cfv
    #
    @0
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @1
    wral
    #
    w3a
    #
    vx
    wex
    #
    vf
    cab
    vg
    cv
    #
    vz
    cv
    #
    wfn
    #
    @17
    cA
    wss
    #
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @17
    wss
    #
    vw
    @17
    wral
    #
    wa
    #
    @20
    @16
    cfv
    #
    @16
    @21
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @17
    wral
    #
    w3a
    #
    vz
    wex
    #
    vg
    cab
    wfrlem1.1
    @15
    @31
    vf
    vg
    vf
    vg
    weq
    #
    @15
    @16
    @1
    wfn
    #
    @8
    @4
    @16
    cfv
    #
    @16
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @1
    wral
    #
    w3a
    #
    vx
    wex
    @31
    @32
    @14
    @39
    vx
    @32
    @2
    @33
    @13
    @38
    @8
    @1
    @0
    @16
    fneq1
    @32
    @12
    @37
    vy
    @1
    @32
    @9
    @34
    @11
    @36
    @4
    @0
    @16
    fveq1
    @32
    @10
    @35
    cF
    @0
    @16
    @5
    reseq1
    fveq2d
    eqeq12d
    ralbidv
    3anbi13d
    exbidv
    @39
    @30
    vx
    vz
    vx
    vz
    weq
    #
    @33
    @18
    @8
    @24
    @38
    @29
    @1
    @17
    @16
    fneq2
    @40
    @3
    @19
    @7
    @23
    @1
    @17
    cA
    sseq1
    @40
    @7
    @5
    @17
    wss
    #
    vy
    @17
    wral
    @23
    @6
    @41
    vy
    @1
    @17
    @1
    @17
    @5
    sseq2
    raleqbi1dv
    @41
    @22
    vy
    vw
    @17
    vy
    vw
    weq
    #
    @5
    @21
    @17
    cA
    cR
    @4
    @20
    predeq3
    #
    sseq1d
    cbvralv
    syl6bb
    anbi12d
    @40
    @38
    @37
    vy
    @17
    wral
    @29
    @37
    vy
    @1
    @17
    raleq
    @37
    @28
    vy
    vw
    @17
    @42
    @34
    @25
    @36
    @27
    @4
    @20
    @16
    fveq2
    @42
    @35
    @26
    cF
    @42
    @5
    @21
    @16
    @43
    reseq2d
    fveq2d
    eqeq12d
    cbvralv
    syl6bb
    3anbi123d
    cbvexv
    syl6bb
    cbvabv
    eqtri
end
