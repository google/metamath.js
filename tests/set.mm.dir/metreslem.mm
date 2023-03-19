include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "cres.mm"
include "cin.mm"
include "resdmres.mm"
include "ineq2.mm"
include "dmres.mm"
include "inxp.mm"
include "incom.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "reseq2d.mm"
include "syl5eqr.mm"

theorem metreslem
  let cD: class D
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cC: class C


  assert |- ( dom D = ( X X. X ) -> ( D |` ( R X. R ) ) = ( D |` ( ( X i^i R ) X. ( X i^i R ) ) ) )

  proof
    cD
    cdm
    #
    cX
    cX
    cxp
    #
    wceq
    #
    cD
    cR
    cR
    cxp
    #
    cres
    #
    cD
    @4
    cdm
    #
    cres
    cD
    cX
    cR
    cin
    #
    @6
    cxp
    #
    cres
    cD
    @3
    resdmres
    @2
    @5
    @7
    cD
    @2
    @3
    @0
    cin
    @3
    @1
    cin
    #
    @5
    @7
    @0
    @1
    @3
    ineq2
    cD
    @3
    dmres
    @1
    @3
    cin
    @7
    @8
    cX
    cX
    cR
    cR
    inxp
    @1
    @3
    incom
    eqtr3i
    3eqtr4g
    reseq2d
    syl5eqr
end
