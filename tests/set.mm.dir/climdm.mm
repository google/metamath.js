include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "wfun.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "fclim.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "mp2b.mm"

theorem climdm
  let cF: class F


  assert |- ( F e. dom ~~> <-> F ~~> ( ~~> ` F ) )

  proof
    cli
    cdm
    #
    cc
    cli
    wf
    cli
    wfun
    cF
    @0
    wcel
    cF
    cF
    cli
    cfv
    cli
    wbr
    wb
    fclim
    @0
    cc
    cli
    ffun
    cF
    cli
    funfvbrb
    mp2b
end
