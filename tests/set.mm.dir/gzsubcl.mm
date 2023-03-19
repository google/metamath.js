include "cgz.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "gzcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "gznegcl.mm"
include "gzaddcl.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem gzsubcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Z[i] /\ B e. Z[i] ) -> ( A - B ) e. Z[i] )

  proof
    cA
    cgz
    wcel
    #
    cB
    cgz
    wcel
    #
    wa
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cgz
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @3
    @4
    wceq
    @1
    cA
    gzcn
    cB
    gzcn
    cA
    cB
    negsub
    syl2an
    @1
    @0
    @2
    cgz
    wcel
    @3
    cgz
    wcel
    cB
    gznegcl
    cA
    @2
    gzaddcl
    sylan2
    eqeltrrd
end
