include "cfin3.mm"
include "wcel.mm"
include "cpw.mm"
include "cfin4.mm"
include "com.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "isfin3.mm"
include "cdom.mm"
include "isfin4-2.mm"
include "ibi.mm"
include "cvv.mm"
include "csdm.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "3syl.mm"
include "wdompwdom.mm"
include "domtr.mm"
include "syl2anc.mm"
include "nsyl.mm"
include "sylbi.mm"

theorem isfin32i
  let cA: class A


  assert |- ( A e. Fin3 -> -. _om ~<_* A )

  proof
    cA
    cfin3
    wcel
    cA
    cpw
    #
    cfin4
    wcel
    #
    com
    cA
    cwdom
    wbr
    #
    wn
    cA
    isfin3
    @1
    com
    @0
    cdom
    wbr
    #
    @2
    @1
    @3
    wn
    @0
    cfin4
    isfin4-2
    ibi
    @2
    com
    com
    cpw
    #
    cdom
    wbr
    #
    @4
    @0
    cdom
    wbr
    @3
    @2
    com
    cvv
    wcel
    com
    @4
    csdm
    wbr
    @5
    com
    cA
    cwdom
    relwdom
    brrelexi
    com
    cvv
    canth2g
    com
    @4
    sdomdom
    3syl
    com
    cA
    wdompwdom
    com
    @4
    @0
    domtr
    syl2anc
    nsyl
    sylbi
end
