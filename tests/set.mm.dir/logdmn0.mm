include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "crp.mm"
include "0nrp.mm"
include "cr.mm"
include "0re.mm"
include "cc.mm"
include "wi.mm"
include "ellogdm.mm"
include "simprbi.mm"
include "mpi.mm"
include "mto.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"

theorem logdmn0
  let cA: class A
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( A e. D -> A =/= 0 )

  proof
    cA
    cD
    wcel
    #
    cA
    cc0
    cA
    cc0
    wceq
    @0
    cc0
    cD
    wcel
    #
    @1
    cc0
    crp
    wcel
    #
    0nrp
    @1
    cc0
    cr
    wcel
    #
    @2
    0re
    @1
    cc0
    cc
    wcel
    @3
    @2
    wi
    cc0
    cD
    logcn.d
    ellogdm
    simprbi
    mpi
    mto
    cA
    cc0
    cD
    eleq1
    mtbiri
    necon2ai
end
