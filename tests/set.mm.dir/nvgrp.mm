include "cnv.mm"
include "wcel.mm"
include "cablo.mm"
include "cgr.mm"
include "nvablo.mm"
include "ablogrpo.mm"
include "syl.mm"

theorem nvgrp
  let cU: class U
  let cG: class G
  assume nvabl.1: |- G = ( +v ` U )


  assert |- ( U e. NrmCVec -> G e. GrpOp )

  proof
    cU
    cnv
    wcel
    cG
    cablo
    wcel
    cG
    cgr
    wcel
    cU
    cG
    nvabl.1
    nvablo
    cG
    ablogrpo
    syl
end
