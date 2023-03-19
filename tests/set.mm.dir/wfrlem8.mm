include "cpred.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wfrdmss.mm"
include "predpredss.mm"
include "ax-mp.mm"
include "biantru.mm"
include "preddif.mm"
include "eqeq1i.mm"
include "ssdif0.mm"
include "bitr4i.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem wfrlem8
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wfrlem6.1: |- F = wrecs ( R , A , G )


  assert |- ( Pred ( R , ( A \ dom F ) , X ) = (/) <-> Pred ( R , A , X ) = Pred ( R , dom F , X ) )

  proof
    cA
    cR
    cX
    cpred
    #
    cF
    cdm
    #
    cR
    cX
    cpred
    #
    wss
    #
    @3
    @2
    @0
    wss
    #
    wa
    cA
    @1
    cdif
    cR
    cX
    cpred
    #
    c0
    wceq
    #
    @0
    @2
    wceq
    @4
    @3
    @1
    cA
    wss
    @4
    cA
    cR
    cF
    cG
    wfrlem6.1
    wfrdmss
    @1
    cA
    cR
    cX
    predpredss
    ax-mp
    biantru
    @6
    @0
    @2
    cdif
    #
    c0
    wceq
    @3
    @5
    @7
    c0
    cA
    @1
    cR
    cX
    preddif
    eqeq1i
    @0
    @2
    ssdif0
    bitr4i
    @0
    @2
    eqss
    3bitr4i
end
