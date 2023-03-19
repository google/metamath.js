include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "ctopn.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "cha.mm"
include "xrge0topn.mm"
include "wcel.mm"
include "cvv.mm"
include "xrhaus.mm"
include "ovex.mm"
include "resthaus.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem xrge0haus



  assert |- ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) e. Haus

  proof
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    ctopn
    cfv
    cle
    cordt
    cfv
    #
    @0
    crest
    co
    #
    cha
    xrge0topn
    @1
    cha
    wcel
    @0
    cvv
    wcel
    @2
    cha
    wcel
    xrhaus
    cc0
    cpnf
    cicc
    ovex
    @0
    @1
    cvv
    resthaus
    mp2an
    eqeltri
end
