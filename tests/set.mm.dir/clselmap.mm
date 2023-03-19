include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "clsf2.mm"
include "cvv.mm"
include "topopn.mm"
include "pwexg.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem clselmap
  let cJ: class J
  let cK: class K
  let cX: class X
  assume clselmap.x: |- X = U. J
  assume clselmap.k: |- K = ( cls ` J )


  assert |- ( J e. Top -> K e. ( ~P X ^m ~P X ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    cX
    cpw
    #
    @1
    cmap
    co
    wcel
    @1
    @1
    cK
    wf
    cJ
    cK
    cX
    clselmap.x
    clselmap.k
    clsf2
    @0
    @1
    @1
    cK
    cvv
    cvv
    @0
    cX
    cJ
    wcel
    @1
    cvv
    wcel
    cJ
    cX
    clselmap.x
    topopn
    cX
    cJ
    pwexg
    syl
    #
    @2
    elmapd
    mpbird
end
