include "clo.mm"
include "wcel.mm"
include "ccop.mm"
include "cbo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "lnopcnbd.mm"
include "elbdop2.mm"
include "baib.mm"
include "bitrd.mm"

theorem lnopcnre
  let cT: class T


  assert |- ( T e. LinOp -> ( T e. ContOp <-> ( normop ` T ) e. RR ) )

  proof
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    cT
    cbo
    wcel
    #
    cT
    cnop
    cfv
    cr
    wcel
    #
    cT
    lnopcnbd
    @1
    @0
    @2
    cT
    elbdop2
    baib
    bitrd
end
