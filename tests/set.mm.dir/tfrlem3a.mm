include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "fneq12.mm"
include "simpll.mm"
include "simpr.mm"
include "fveq12d.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "simplr.mm"
include "cbvraldva2.mm"
include "anbi12d.mm"
include "cbvrexdva.mm"
include "elab2.mm"

theorem tfrlem3a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cG: class G
  let vg: setvar g
  assume tfrlem3.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }
  assume tfrlem3.2: |- G e. _V

  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint A g
  disjoint f g
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  assert |- ( G e. A <-> E. z e. On ( G Fn z /\ A. w e. z ( G ` w ) = ( F ` ( G |` w ) ) ) )

  proof
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    @0
    cfv
    #
    @0
    @3
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
    wa
    #
    vx
    con0
    wrex
    cG
    vz
    cv
    #
    wfn
    #
    vw
    cv
    #
    cG
    cfv
    #
    cG
    @12
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @10
    wral
    #
    wa
    #
    vz
    con0
    wrex
    vf
    cG
    cA
    tfrlem3.2
    @0
    cG
    wceq
    #
    @9
    @18
    vx
    vz
    con0
    @19
    @1
    @10
    wceq
    #
    wa
    #
    @2
    @11
    @8
    @17
    @1
    @10
    @0
    cG
    fneq12
    @21
    @7
    @16
    vy
    vw
    @1
    @10
    @21
    @3
    @12
    wceq
    #
    wa
    #
    @4
    @13
    @6
    @15
    @23
    @3
    @12
    @0
    cG
    @19
    @20
    @22
    simpll
    #
    @21
    @22
    simpr
    #
    fveq12d
    @23
    @5
    @14
    cF
    @23
    @0
    cG
    @3
    @12
    @24
    @25
    reseq12d
    fveq2d
    eqeq12d
    @19
    @20
    @22
    simplr
    cbvraldva2
    anbi12d
    cbvrexdva
    tfrlem3.1
    elab2
end
