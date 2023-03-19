include "crglmod.mm"
include "cfv.mm"
include "cbs.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "clidl.mm"
include "clss.mm"
include "lidlval.mm"
include "lssss.mm"

theorem lidlss
  let cB: class B
  let cU: class U
  let cI: class I
  let cW: class W
  assume lidlss.b: |- B = ( Base ` W )
  assume lidlss.i: |- I = ( LIdeal ` W )


  assert |- ( U e. I -> U C_ B )

  proof
    cI
    cU
    cB
    cW
    crglmod
    cfv
    #
    cB
    cW
    cbs
    cfv
    @0
    cbs
    cfv
    lidlss.b
    cW
    rlmbas
    eqtri
    cI
    cW
    clidl
    cfv
    @0
    clss
    cfv
    lidlss.i
    cW
    lidlval
    eqtri
    lssss
end
