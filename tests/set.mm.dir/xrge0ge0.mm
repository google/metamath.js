include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "elxrge0.mm"
include "biimpi.mm"
include "simprd.mm"

theorem xrge0ge0
  let cA: class A


  assert |- ( A e. ( 0 [,] +oo ) -> 0 <_ A )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    wcel
    #
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    @0
    @1
    @2
    wa
    cA
    elxrge0
    biimpi
    simprd
end
