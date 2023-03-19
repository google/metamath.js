include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "cxrs.mm"
include "cress.mm"
include "ctopn.mm"
include "eqid.mm"
include "xrstopn.mm"
include "resstopn.mm"
include "eqcomi.mm"

theorem xrge0topn



  assert |- ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  proof
    cle
    cordt
    cfv
    #
    cc0
    cpnf
    cicc
    co
    #
    crest
    co
    cxrs
    @1
    cress
    co
    #
    ctopn
    cfv
    @1
    @2
    @0
    cxrs
    @2
    eqid
    xrstopn
    resstopn
    eqcomi
end
