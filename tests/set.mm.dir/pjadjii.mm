include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "cva.mm"
include "co.mm"
include "csp.mm"
include "caddc.mm"
include "ccj.mm"
include "cc0.mm"
include "cch.mm"
include "wcel.mm"
include "wceq.mm"
include "pjorthi.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "cj0.mm"
include "eqtri.mm"
include "choccli.mm"
include "pjhclii.mm"
include "his1i.mm"
include "3eqtr4ri.mm"
include "oveq2i.mm"
include "chil.mm"
include "his7.mm"
include "mp3an.mm"
include "ax-his2.mm"
include "3eqtr4i.mm"
include "pjpji.mm"
include "oveq1i.mm"

theorem pjadjii
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjadj.3: |- B e. ~H


  assert |- ( ( ( projh ` H ) ` A ) .ih B ) = ( A .ih ( ( projh ` H ) ` B ) )

  proof
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cB
    @0
    cfv
    #
    cB
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    cva
    co
    #
    csp
    co
    #
    @1
    cA
    @4
    cfv
    #
    cva
    co
    #
    @2
    csp
    co
    #
    @1
    cB
    csp
    co
    cA
    @2
    csp
    co
    @1
    @2
    csp
    co
    #
    @1
    @5
    csp
    co
    #
    caddc
    co
    #
    @11
    @8
    @2
    csp
    co
    #
    caddc
    co
    #
    @7
    @10
    @12
    @14
    @11
    caddc
    @2
    @8
    csp
    co
    #
    ccj
    cfv
    #
    cc0
    @14
    @12
    @17
    cc0
    ccj
    cfv
    cc0
    @16
    cc0
    ccj
    cH
    cch
    wcel
    #
    @16
    cc0
    wceq
    pjidm.1
    cB
    cA
    cH
    pjadj.3
    pjidm.2
    pjorthi
    ax-mp
    fveq2i
    cj0
    eqtri
    @8
    @2
    cA
    @3
    cH
    pjidm.1
    choccli
    #
    pjidm.2
    pjhclii
    #
    cB
    cH
    pjidm.1
    pjadj.3
    pjhclii
    #
    his1i
    @18
    @12
    cc0
    wceq
    pjidm.1
    cA
    cB
    cH
    pjidm.2
    pjadj.3
    pjorthi
    ax-mp
    3eqtr4ri
    oveq2i
    @1
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    @5
    chil
    wcel
    @7
    @13
    wceq
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    @21
    cB
    @3
    @19
    pjadj.3
    pjhclii
    @1
    @2
    @5
    his7
    mp3an
    @22
    @8
    chil
    wcel
    @23
    @10
    @15
    wceq
    @24
    @20
    @21
    @1
    @8
    @2
    ax-his2
    mp3an
    3eqtr4i
    cB
    @6
    @1
    csp
    cB
    cH
    pjidm.1
    pjadj.3
    pjpji
    oveq2i
    cA
    @9
    @2
    csp
    cA
    cH
    pjidm.1
    pjidm.2
    pjpji
    oveq1i
    3eqtr4i
end
