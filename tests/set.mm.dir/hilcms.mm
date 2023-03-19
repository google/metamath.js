include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "hhims.mm"
include "hhcms.mm"

theorem hilcms
  let cD: class D
  assume hilcms.1: |- D = ( normh o. -h )


  assert |- D e. ( CMet ` ~H )

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
    hilcms.1
    hhims
    hhcms
end
