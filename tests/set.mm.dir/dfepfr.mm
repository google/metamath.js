include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "dffr2.mm"
include "wel.mm"
include "epel.mm"
include "rabbii.mm"
include "dfin5.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitri.mm"

theorem dfepfr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( _E Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x ( x i^i y ) = (/) ) )

  proof
    cA
    cep
    wfr
    vx
    cv
    #
    cA
    wss
    @0
    c0
    wne
    wa
    #
    vz
    cv
    vy
    cv
    #
    cep
    wbr
    #
    vz
    @0
    crab
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    @1
    @0
    @2
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    vx
    vy
    vz
    cA
    cep
    dffr2
    @7
    @11
    vx
    @6
    @10
    @1
    @5
    @9
    vy
    @0
    @4
    @8
    c0
    @4
    vz
    vy
    wel
    #
    vz
    @0
    crab
    @8
    @3
    @12
    vz
    @0
    vz
    vy
    epel
    rabbii
    vz
    @0
    @2
    dfin5
    eqtr4i
    eqeq1i
    rexbii
    imbi2i
    albii
    bitri
end
