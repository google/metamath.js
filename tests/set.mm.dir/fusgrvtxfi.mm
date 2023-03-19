include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cfn.mm"
include "isfusgr.mm"
include "simprbi.mm"

theorem fusgrvtxfi
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume isfusgr.v: |- V = ( Vtx ` G )


  assert |- ( G e. FinUSGraph -> V e. Fin )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    cV
    cfn
    wcel
    cG
    cV
    isfusgr.v
    isfusgr
    simprbi
end
