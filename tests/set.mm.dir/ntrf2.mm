include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "ntrf.mm"
include "c0.mm"
include "cpr.mm"
include "wss.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "toptopon.mm"
include "topgele.mm"
include "sylbi.mm"
include "simprd.mm"
include "fssd.mm"

theorem ntrf2
  let cI: class I
  let cJ: class J
  let cX: class X
  assume ntrrn.x: |- X = U. J
  assume ntrrn.i: |- I = ( int ` J )


  assert |- ( J e. Top -> I : ~P X --> ~P X )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cpw
    #
    cJ
    @1
    cI
    cI
    cJ
    cX
    ntrrn.x
    ntrrn.i
    ntrf
    @0
    c0
    cX
    cpr
    cJ
    wss
    #
    cJ
    @1
    wss
    #
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @2
    @3
    wa
    cJ
    cX
    ntrrn.x
    toptopon
    cJ
    cX
    topgele
    sylbi
    simprd
    fssd
end
