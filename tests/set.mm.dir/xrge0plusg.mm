include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cxad.mm"
include "cxrs.mm"
include "cress.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "ovex.mm"
include "eqid.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"

theorem xrge0plusg



  assert |- +e = ( +g ` ( RR*s |`s ( 0 [,] +oo ) ) )

  proof
    cc0
    cpnf
    cicc
    co
    #
    cvv
    wcel
    cxad
    cxrs
    @0
    cress
    co
    #
    cplusg
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    @0
    cxad
    cxrs
    @1
    cvv
    @1
    eqid
    xrsadd
    ressplusg
    ax-mp
end
