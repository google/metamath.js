include "cv.mm"
include "wcel.mm"
include "wa.mm"
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
include "adantr.mm"
include "wb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elabg.mm"
include "adantl.mm"
include "mpbird.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "eqeq2d.mm"
include "cbvrex.mm"
include "abbii.mm"
include "syl6eleqr.mm"

theorem elabrexg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ( x e. A /\ B e. V ) -> B e. { y | E. x e. A y = B } )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cV
    wcel
    #
    wa
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
    @4
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @3
    cB
    @9
    wcel
    #
    cB
    @6
    wceq
    #
    vz
    cA
    wrex
    #
    @1
    @14
    @2
    @1
    wtru
    @14
    tru
    @13
    wtru
    vz
    @0
    cA
    @5
    @0
    wceq
    #
    @13
    wtru
    @13
    vx
    vz
    vx
    @5
    cB
    csbeq1a
    #
    equcoms
    @15
    a1tru
    2thd
    rspcev
    mpan2
    adantr
    @2
    @12
    @14
    wb
    @1
    @8
    @14
    vy
    cB
    cV
    @10
    @7
    @13
    vz
    cA
    @4
    cB
    @6
    eqeq1
    rexbidv
    elabg
    adantl
    mpbird
    @11
    @8
    vy
    @10
    @7
    vx
    vz
    cA
    @10
    vz
    nfv
    vx
    @4
    @6
    vx
    @5
    cB
    nfcsb1v
    nfeq2
    @0
    @5
    wceq
    cB
    @6
    @4
    @16
    eqeq2d
    cbvrex
    abbii
    syl6eleqr
end
