include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "hhims.mm"
include "hhmetdval.mm"

theorem hilmetdval
  let cA: class A
  let cB: class B
  let cD: class D
  assume hilmet.1: |- D = ( normh o. -h )


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A D B ) = ( normh ` ( A -h B ) ) )

  proof
    cA
    cB
    cD
    cva
    csm
    cop
    cno
    cop
    #
    @0
    eqid
    #
    cD
    @0
    @1
    hilmet.1
    hhims
    hhmetdval
end
