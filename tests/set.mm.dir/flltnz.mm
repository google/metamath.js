include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wn.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "reflcl.mm"
include "adantr.mm"
include "simpl.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "fllelt.mm"
include "simpld.mm"
include "wceq.mm"
include "simpr.mm"
include "wb.mm"
include "flidz.mm"
include "mtbird.mm"
include "neqned.mm"
include "necomd.mm"
include "leneltd.mm"

theorem flltnz
  let cA: class A


  assert |- ( ( A e. RR /\ -. A e. ZZ ) -> ( |_ ` A ) < A )

  proof
    cA
    cr
    wcel
    #
    cA
    cz
    wcel
    #
    wn
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cA
    @0
    @4
    cr
    wcel
    @2
    cA
    reflcl
    adantr
    @0
    @2
    simpl
    @3
    @4
    cA
    cle
    wbr
    #
    cA
    @4
    c1
    caddc
    co
    clt
    wbr
    #
    @0
    @5
    @6
    wa
    @2
    cA
    fllelt
    adantr
    simpld
    @3
    @4
    cA
    @3
    @4
    cA
    @3
    @4
    cA
    wceq
    #
    @1
    @0
    @2
    simpr
    @0
    @7
    @1
    wb
    @2
    cA
    flidz
    adantr
    mtbird
    neqned
    necomd
    leneltd
end
