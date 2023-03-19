include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cfn.mm"
include "wcel.mm"
include "id.mm"
include "com.mm"
include "cen.mm"
include "csdm.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "sylbi.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "sylancl.mm"
include "ovolctb2.mm"
include "syl2anr.mm"

theorem ovolfi
  let cA: class A


  assert |- ( ( A e. Fin /\ A C_ RR ) -> ( vol* ` A ) = 0 )

  proof
    cA
    cr
    wss
    #
    @0
    cA
    cn
    cdom
    wbr
    #
    cA
    covol
    cfv
    cc0
    wceq
    cA
    cfn
    wcel
    #
    @0
    id
    @2
    cA
    com
    cdom
    wbr
    #
    com
    cn
    cen
    wbr
    @1
    @2
    cA
    com
    csdm
    wbr
    @3
    cA
    isfinite
    cA
    com
    sdomdom
    sylbi
    cn
    com
    nnenom
    ensymi
    cA
    com
    cn
    domentr
    sylancl
    cA
    ovolctb2
    syl2anr
end
