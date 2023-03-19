include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "wex.mm"
include "cab.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cuni.mm"
include "rnopab.mm"
include "cnvepres.mm"
include "rneqi.mm"
include "wrex.mm"
include "dfuni2.mm"
include "df-rex.mm"
include "abbii.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem rncnvepres
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ran ( `' _E |` A ) = U. A

  proof
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    @0
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    crn
    @2
    vx
    wex
    #
    vy
    cab
    #
    cep
    ccnv
    cA
    cres
    #
    crn
    cA
    cuni
    #
    @2
    vx
    vy
    rnopab
    @6
    @3
    vx
    vy
    cA
    cnvepres
    rneqi
    @7
    @1
    vx
    cA
    wrex
    #
    vy
    cab
    @5
    vy
    vx
    cA
    dfuni2
    @8
    @4
    vy
    @1
    vx
    cA
    df-rex
    abbii
    eqtri
    3eqtr4i
end
