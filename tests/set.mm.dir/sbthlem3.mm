include "cv.mm"
include "crn.mm"
include "wss.mm"
include "cuni.mm"
include "cdif.mm"
include "cima.mm"
include "wa.mm"
include "wceq.mm"
include "sbthlem2.mm"
include "sbthlem1.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"
include "difeq2d.mm"
include "wi.mm"
include "imassrn.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqtr2d.mm"

theorem sbthlem3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ran g C_ A -> ( g " ( B \ ( f " U. D ) ) ) = ( A \ U. D ) )

  proof
    vg
    cv
    #
    crn
    #
    cA
    wss
    #
    cA
    cD
    cuni
    #
    cdif
    cA
    cA
    @0
    cB
    vf
    cv
    @3
    cima
    cdif
    #
    cima
    #
    cdif
    #
    cdif
    #
    @5
    @2
    @3
    @6
    cA
    @2
    @3
    @6
    wss
    #
    @6
    @3
    wss
    #
    wa
    @3
    @6
    wceq
    @2
    @9
    @8
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem2
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem1
    jctil
    @3
    @6
    eqss
    sylibr
    difeq2d
    @2
    @5
    cA
    wss
    #
    @7
    @5
    wceq
    @5
    @1
    wss
    @2
    @10
    wi
    @0
    @4
    imassrn
    @5
    @1
    cA
    sstr2
    ax-mp
    @5
    cA
    dfss4
    sylib
    eqtr2d
end
