include "covol.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "wral.mm"
include "cab.mm"
include "cres.mm"
include "cdm.mm"
include "cvol.mm"
include "resdmres.mm"
include "df-vol.mm"
include "dmeqi.mm"
include "reseq2i.mm"
include "3eqtr4ri.mm"

theorem volres
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- vol = ( vol* |` dom vol )

  proof
    covol
    covol
    vy
    cv
    #
    covol
    cfv
    @0
    vx
    cv
    #
    cin
    covol
    cfv
    @0
    @1
    cdif
    covol
    cfv
    caddc
    co
    wceq
    vy
    covol
    ccnv
    cr
    cima
    wral
    vx
    cab
    #
    cres
    #
    cdm
    #
    cres
    @3
    covol
    cvol
    cdm
    #
    cres
    cvol
    covol
    @2
    resdmres
    @5
    @4
    covol
    cvol
    @3
    vx
    vy
    df-vol
    #
    dmeqi
    reseq2i
    @6
    3eqtr4ri
end
