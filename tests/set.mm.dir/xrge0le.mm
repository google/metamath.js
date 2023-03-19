include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cle.mm"
include "cxrs.mm"
include "cress.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "ovex.mm"
include "eqid.mm"
include "xrsle.mm"
include "ressle.mm"
include "ax-mp.mm"

theorem xrge0le



  assert |- <_ = ( le ` ( RR*s |`s ( 0 [,] +oo ) ) )

  proof
    cc0
    cpnf
    cicc
    co
    #
    cvv
    wcel
    cle
    cxrs
    @0
    cress
    co
    #
    cple
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    @0
    cxrs
    cle
    cvv
    @1
    @1
    eqid
    xrsle
    ressle
    ax-mp
end
