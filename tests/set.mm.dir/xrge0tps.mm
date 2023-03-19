include "cxrs.mm"
include "ctps.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cvv.mm"
include "cress.mm"
include "xrstps.mm"
include "ovex.mm"
include "resstps.mm"
include "mp2an.mm"

theorem xrge0tps



  assert |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopSp

  proof
    cxrs
    ctps
    wcel
    cc0
    cpnf
    cicc
    co
    #
    cvv
    wcel
    cxrs
    @0
    cress
    co
    ctps
    wcel
    xrstps
    cc0
    cpnf
    cicc
    ovex
    @0
    cxrs
    cvv
    resstps
    mp2an
end
