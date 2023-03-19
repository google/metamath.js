include "cfv.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "eqid.mm"
include "tz6.12i.mm"
include "mpi.mm"
include "necon1bi.mm"
include "orri.mm"

theorem fvbr0
  let cF: class F
  let cX: class X


  assert |- ( X F ( F ` X ) \/ ( F ` X ) = (/) )

  proof
    cX
    cX
    cF
    cfv
    #
    cF
    wbr
    #
    @0
    c0
    wceq
    @1
    @0
    c0
    @0
    c0
    wne
    @0
    @0
    wceq
    @1
    @0
    eqid
    cX
    @0
    cF
    tz6.12i
    mpi
    necon1bi
    orri
end
