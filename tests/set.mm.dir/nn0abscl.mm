include "cz.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "absz.mm"
include "syl.mm"
include "ibi.mm"
include "cc.mm"
include "zcn.mm"
include "absge0.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem nn0abscl
  let cA: class A


  assert |- ( A e. ZZ -> ( abs ` A ) e. NN0 )

  proof
    cA
    cz
    wcel
    #
    cA
    cabs
    cfv
    #
    cz
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @1
    cn0
    wcel
    @0
    @2
    @0
    cA
    cr
    wcel
    @0
    @2
    wb
    cA
    zre
    cA
    absz
    syl
    ibi
    @0
    cA
    cc
    wcel
    @3
    cA
    zcn
    cA
    absge0
    syl
    @1
    elnn0z
    sylanbrc
end
