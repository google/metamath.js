include "cv.mm"
include "cin.mm"
include "csn.mm"
include "wcel.mm"
include "wral.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "elsni.mm"
include "ineqan12d.mm"
include "inidm.mm"
include "syl6eq.mm"
include "vex.mm"
include "inex1.mm"
include "elsn.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "inficl.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem fisn
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V


  assert |- ( fi ` { A } ) = { A }

  proof
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cA
    csn
    #
    wcel
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    @3
    cfi
    cfv
    @3
    wceq
    #
    @4
    vx
    vy
    @3
    @0
    @3
    wcel
    #
    @1
    @3
    wcel
    #
    wa
    #
    @2
    cA
    wceq
    @4
    @9
    @2
    cA
    cA
    cin
    cA
    @7
    @8
    @0
    cA
    @1
    cA
    @0
    cA
    elsni
    @1
    cA
    elsni
    ineqan12d
    cA
    inidm
    syl6eq
    @2
    cA
    @0
    @1
    vx
    vex
    inex1
    elsn
    sylibr
    rgen2a
    @3
    cvv
    wcel
    @5
    @6
    wb
    cA
    snex
    vx
    vy
    @3
    cvv
    inficl
    ax-mp
    mpbi
end
