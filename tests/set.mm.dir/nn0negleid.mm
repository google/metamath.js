include "cn0.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "nn0re.mm"
include "renegcld.mm"
include "0red.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "le0neg2d.mm"
include "mpbid.mm"
include "letrd.mm"

theorem nn0negleid
  let cA: class A


  assert |- ( A e. NN0 -> -u A <_ A )

  proof
    cA
    cn0
    wcel
    #
    cA
    cneg
    #
    cc0
    cA
    @0
    cA
    cA
    nn0re
    #
    renegcld
    @0
    0red
    @2
    @0
    cc0
    cA
    cle
    wbr
    @1
    cc0
    cle
    wbr
    cA
    nn0ge0
    #
    @0
    cA
    @2
    le0neg2d
    mpbid
    @3
    letrd
end
