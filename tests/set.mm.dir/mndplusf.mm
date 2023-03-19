include "cmnd.mm"
include "wcel.mm"
include "cmgm.mm"
include "cxp.mm"
include "wf.mm"
include "mndmgm.mm"
include "mgmplusf.mm"
include "syl.mm"

theorem mndplusf
  let cB: class B
  let c.pd: class .+^
  let cG: class G
  assume mndplusf.1: |- B = ( Base ` G )
  assume mndplusf.2: |- .+^ = ( +f ` G )


  assert |- ( G e. Mnd -> .+^ : ( B X. B ) --> B )

  proof
    cG
    cmnd
    wcel
    cG
    cmgm
    wcel
    cB
    cB
    cxp
    cB
    c.pd
    wf
    cG
    mndmgm
    cB
    c.pd
    cG
    mndplusf.1
    mndplusf.2
    mgmplusf
    syl
end
