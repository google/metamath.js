include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "ccj.mm"
include "csp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "c2.mm"
include "csqrt.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "eleq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ax-1cn.mm"
include "abs1.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "normlem7.mm"
include "dedth.mm"

theorem normlem7tALT
  let cA: class A
  let cB: class B
  let cS: class S
  assume normlem7t.1: |- A e. ~H
  assume normlem7t.2: |- B e. ~H


  assert |- ( ( S e. CC /\ ( abs ` S ) = 1 ) -> ( ( ( * ` S ) x. ( A .ih B ) ) + ( S x. ( B .ih A ) ) ) <_ ( 2 x. ( ( sqrt ` ( B .ih B ) ) x. ( sqrt ` ( A .ih A ) ) ) ) )

  proof
    cS
    cc
    wcel
    #
    cS
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cS
    ccj
    cfv
    #
    cA
    cB
    csp
    co
    #
    cmul
    co
    #
    cS
    cB
    cA
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c2
    cB
    cB
    csp
    co
    csqrt
    cfv
    cA
    cA
    csp
    co
    csqrt
    cfv
    cmul
    co
    cmul
    co
    #
    cle
    wbr
    @3
    cS
    c1
    cif
    #
    ccj
    cfv
    #
    @5
    cmul
    co
    #
    @11
    @7
    cmul
    co
    #
    caddc
    co
    #
    @10
    cle
    wbr
    cS
    c1
    cS
    @11
    wceq
    #
    @9
    @15
    @10
    cle
    @16
    @6
    @13
    @8
    @14
    caddc
    @16
    @4
    @12
    @5
    cmul
    cS
    @11
    ccj
    fveq2
    oveq1d
    cS
    @11
    @7
    cmul
    oveq1
    oveq12d
    breq1d
    @11
    cA
    cB
    @11
    cc
    wcel
    #
    @11
    cabs
    cfv
    #
    c1
    wceq
    #
    @3
    @17
    @19
    wa
    c1
    cc
    wcel
    #
    c1
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    cS
    c1
    @16
    @0
    @17
    @2
    @19
    cS
    @11
    cc
    eleq1
    @16
    @1
    @18
    c1
    cS
    @11
    cabs
    fveq2
    eqeq1d
    anbi12d
    c1
    @11
    wceq
    #
    @20
    @17
    @22
    @19
    c1
    @11
    cc
    eleq1
    @23
    @21
    @18
    c1
    c1
    @11
    cabs
    fveq2
    eqeq1d
    anbi12d
    @20
    @22
    ax-1cn
    abs1
    pm3.2i
    elimhyp
    #
    simpli
    normlem7t.1
    normlem7t.2
    @17
    @19
    @24
    simpri
    normlem7
    dedth
end
