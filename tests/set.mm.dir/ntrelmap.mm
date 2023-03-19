include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrf2.mm"
include "cvv.mm"
include "topopn.mm"
include "pwexg.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem ntrelmap
  let cI: class I
  let cJ: class J
  let cX: class X
  assume ntrrn.x: |- X = U. J
  assume ntrrn.i: |- I = ( int ` J )


  assert |- ( J e. Top -> I e. ( ~P X ^m ~P X ) )

  proof
    cJ
    ctop
    wcel
    #
    cI
    cX
    cpw
    #
    @1
    cmap
    co
    wcel
    @1
    @1
    cI
    wf
    cI
    cJ
    cX
    ntrrn.x
    ntrrn.i
    ntrf2
    @0
    @1
    @1
    cI
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
    ntrrn.x
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
