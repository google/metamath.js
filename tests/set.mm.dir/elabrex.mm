include "cv.mm"
include "wcel.mm"
include "csb.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wtru.mm"
include "tru.mm"
include "csbeq1a.mm"
include "equcoms.mm"
include "a1tru.mm"
include "2thd.mm"
include "rspcev.mm"
include "mpan2.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "eqeq2d.mm"
include "cbvrex.mm"
include "abbii.mm"
include "syl6eleqr.mm"

theorem elabrex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume elabrex.1: |- B e. _V

  disjoint B y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint y z
  disjoint B z
  disjoint x z
  disjoint A z
  assert |- ( x e. A -> B e. { y | E. x e. A y = B } )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    cB
    vy
    cv
    #
    vx
    vz
    cv
    #
    cB
    csb
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vy
    cab
    #
    @2
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    cB
    @4
    wceq
    #
    vz
    cA
    wrex
    #
    cB
    @7
    wcel
    @1
    wtru
    @11
    tru
    @10
    wtru
    vz
    @0
    cA
    @3
    @0
    wceq
    #
    @10
    wtru
    @10
    vx
    vz
    vx
    @3
    cB
    csbeq1a
    #
    equcoms
    @12
    a1tru
    2thd
    rspcev
    mpan2
    @6
    @11
    vy
    cB
    elabrex.1
    @8
    @5
    @10
    vz
    cA
    @2
    cB
    @4
    eqeq1
    rexbidv
    elab
    sylibr
    @9
    @6
    vy
    @8
    @5
    vx
    vz
    cA
    @8
    vz
    nfv
    vx
    @2
    @4
    vx
    @3
    cB
    nfcsb1v
    nfeq2
    @0
    @3
    wceq
    cB
    @4
    @2
    @13
    eqeq2d
    cbvrex
    abbii
    syl6eleqr
end
