include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "hhims.mm"
include "hhmet.mm"

theorem hilmet
  let cD: class D
  assume hilmet.1: |- D = ( normh o. -h )


  assert |- D e. ( Met ` ~H )

  proof
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
    hhmet
end
