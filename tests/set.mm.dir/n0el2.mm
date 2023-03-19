include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "cdm.mm"
include "wceq.mm"
include "c0.mm"
include "wn.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "dmopab3.mm"
include "n0el.mm"
include "cnvepres.mm"
include "dmeqi.mm"
include "eqeq1i.mm"
include "3bitr4i.mm"

theorem n0el2
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. (/) e. A <-> dom ( `' _E |` A ) = A )

  proof
    vy
    cv
    vx
    cv
    #
    wcel
    #
    vy
    wex
    vx
    cA
    wral
    @0
    cA
    wcel
    @1
    wa
    vx
    vy
    copab
    #
    cdm
    #
    cA
    wceq
    c0
    cA
    wcel
    wn
    cep
    ccnv
    cA
    cres
    #
    cdm
    #
    cA
    wceq
    @1
    vx
    vy
    cA
    dmopab3
    vx
    vy
    cA
    n0el
    @5
    @3
    cA
    @4
    @2
    vx
    vy
    cA
    cnvepres
    dmeqi
    eqeq1i
    3bitr4i
end
