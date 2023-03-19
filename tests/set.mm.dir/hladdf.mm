include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cxp.mm"
include "wf.mm"
include "hlnv.mm"
include "nvgf.mm"
include "syl.mm"

theorem hladdf
  let cU: class U
  let cG: class G
  let cX: class X
  assume hladdf.1: |- X = ( BaseSet ` U )
  assume hladdf.2: |- G = ( +v ` U )


  assert |- ( U e. CHilOLD -> G : ( X X. X ) --> X )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    cX
    cX
    cxp
    cX
    cG
    wf
    cU
    hlnv
    cU
    cG
    cX
    hladdf.1
    hladdf.2
    nvgf
    syl
end
