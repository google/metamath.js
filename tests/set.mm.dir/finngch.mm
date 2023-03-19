include "cfn.mm"
include "wcel.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "cfin4.mm"
include "cfin2.mm"
include "cfin3.mm"
include "fin12.mm"
include "fin23.mm"
include "fin34.mm"
include "3syl.mm"
include "isfin4-3.mm"
include "sylib.mm"
include "canthp1.mm"
include "anim12i.mm"

theorem finngch
  let cA: class A


  assert |- ( ( A e. Fin /\ 1o ~< A ) -> ( A ~< ( A +c 1o ) /\ ( A +c 1o ) ~< ~P A ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cA
    c1o
    ccda
    co
    #
    csdm
    wbr
    #
    c1o
    cA
    csdm
    wbr
    @1
    cA
    cpw
    csdm
    wbr
    @0
    cA
    cfin4
    wcel
    #
    @2
    @0
    cA
    cfin2
    wcel
    cA
    cfin3
    wcel
    @3
    cA
    fin12
    cA
    fin23
    cA
    fin34
    3syl
    cA
    isfin4-3
    sylib
    cA
    canthp1
    anim12i
end
