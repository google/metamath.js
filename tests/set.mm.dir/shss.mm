include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cva.mm"
include "cxp.mm"
include "cima.mm"
include "csm.mm"
include "cc.mm"
include "issh.mm"
include "simplbi.mm"
include "simpld.mm"

theorem shss
  let cH: class H


  assert |- ( H e. SH -> H C_ ~H )

  proof
    cH
    csh
    wcel
    #
    cH
    chil
    wss
    #
    c0v
    cH
    wcel
    #
    @0
    @1
    @2
    wa
    cva
    cH
    cH
    cxp
    cima
    cH
    wss
    csm
    cc
    cH
    cxp
    cima
    cH
    wss
    wa
    cH
    issh
    simplbi
    simpld
end
