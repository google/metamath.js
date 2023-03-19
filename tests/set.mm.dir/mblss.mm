include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ismbl.mm"
include "simplbi.mm"

theorem mblss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. dom vol -> A C_ RR )

  proof
    cA
    cvol
    cdm
    wcel
    cA
    cr
    wss
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    @1
    @0
    cA
    cin
    covol
    cfv
    @0
    cA
    cdif
    covol
    cfv
    caddc
    co
    wceq
    wi
    vx
    cr
    cpw
    wral
    vx
    cA
    ismbl
    simplbi
end
