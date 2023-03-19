include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "0red.mm"
include "abscl.mm"
include "absge0.mm"
include "leltned.mm"
include "abs00.mm"
include "necon3bid.mm"
include "bitr2d.mm"

theorem absgt0
  let cA: class A


  assert |- ( A e. CC -> ( A =/= 0 <-> 0 < ( abs ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    cA
    cabs
    cfv
    #
    clt
    wbr
    @1
    cc0
    wne
    cA
    cc0
    wne
    @0
    cc0
    @1
    @0
    0red
    cA
    abscl
    cA
    absge0
    leltned
    @0
    @1
    cc0
    cA
    cc0
    cA
    abs00
    necon3bid
    bitr2d
end
