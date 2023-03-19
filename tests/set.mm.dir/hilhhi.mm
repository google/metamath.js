include "cnv.mm"
include "wcel.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "wceq.mm"
include "hilnormi.mm"
include "nvop.mm"
include "ax-mp.mm"

theorem hilhhi
  let cU: class U
  assume hilhh.1: |- ~H = ( BaseSet ` U )
  assume hilhh.2: |- +h = ( +v ` U )
  assume hilhh.3: |- .h = ( .sOLD ` U )
  assume hilhh.5: |- .ih = ( .iOLD ` U )
  assume hilhh.9: |- U e. NrmCVec


  assert |- U = <. <. +h , .h >. , normh >.

  proof
    cU
    cnv
    wcel
    cU
    cva
    csm
    cop
    cno
    cop
    wceq
    hilhh.9
    csm
    cU
    cva
    cno
    hilhh.2
    hilhh.3
    cU
    hilhh.1
    hilhh.5
    hilhh.9
    hilnormi
    nvop
    ax-mp
end
