include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "cpw.mm"
include "cldss2.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "ctop.mm"
include "topcld.mm"
include "ax-mp.mm"
include "unissel.mm"
include "mp2an.mm"

theorem unicls
  let cJ: class J
  let cX: class X
  assume unicls.1: |- J e. Top
  assume unicls.2: |- X = U. J


  assert |- U. ( Clsd ` J ) = X

  proof
    cJ
    ccld
    cfv
    #
    cuni
    #
    cX
    wss
    #
    cX
    @0
    wcel
    #
    @1
    cX
    wceq
    @0
    cX
    cpw
    wss
    @2
    cJ
    cX
    unicls.2
    cldss2
    @0
    cX
    sspwuni
    mpbi
    cJ
    ctop
    wcel
    @3
    unicls.1
    cJ
    cX
    unicls.2
    topcld
    ax-mp
    @0
    cX
    unissel
    mp2an
end
