include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "chil.mm"
include "df-hba.mm"
include "hlex.mm"

theorem axhilex-zf
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ~H e. _V

  proof
    cva
    csm
    cop
    cno
    cop
    chil
    df-hba
    hlex
end
