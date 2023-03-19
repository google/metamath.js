include "csn.mm"
include "wor.mm"
include "wpo.mm"
include "wrel.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "elsni.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "3mix2d.mm"
include "rgen2a.mm"
include "df-so.mm"
include "mpbiran2.mm"
include "posn.mm"
include "syl5bb.mm"

theorem sosn
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel R -> ( R Or { A } <-> -. A R A ) )

  proof
    cA
    csn
    #
    cR
    wor
    #
    @0
    cR
    wpo
    #
    cR
    wrel
    cA
    cA
    cR
    wbr
    wn
    @1
    @2
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    weq
    #
    @4
    @3
    cR
    wbr
    #
    w3o
    #
    vy
    @0
    wral
    vx
    @0
    wral
    @8
    vx
    vy
    @0
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    @6
    @5
    @7
    @9
    @10
    @3
    cA
    @4
    @3
    cA
    elsni
    @10
    @4
    cA
    @4
    cA
    elsni
    eqcomd
    sylan9eq
    3mix2d
    rgen2a
    vx
    vy
    @0
    cR
    df-so
    mpbiran2
    cA
    cR
    posn
    syl5bb
end
