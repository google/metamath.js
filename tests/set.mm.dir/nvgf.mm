include "cnv.mm"
include "wcel.mm"
include "cgr.mm"
include "cxp.mm"
include "wfo.mm"
include "wf.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpofo.mm"
include "fof.mm"
include "3syl.mm"

theorem nvgf
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgf.1: |- X = ( BaseSet ` U )
  assume nvgf.2: |- G = ( +v ` U )


  assert |- ( U e. NrmCVec -> G : ( X X. X ) --> X )

  proof
    cU
    cnv
    wcel
    cG
    cgr
    wcel
    cX
    cX
    cxp
    #
    cX
    cG
    wfo
    @0
    cX
    cG
    wf
    cU
    cG
    nvgf.2
    nvgrp
    cG
    cX
    cU
    cG
    cX
    nvgf.1
    nvgf.2
    bafval
    grpofo
    @0
    cX
    cG
    fof
    3syl
end
