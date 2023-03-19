include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "cr.mm"
include "wa.mm"
include "wceq.mm"
include "xnegneg.mm"
include "adantr.mm"
include "xnegrecl.mm"
include "adantl.mm"
include "eqeltrrd.mm"

theorem xnegrecl2
  let cA: class A


  assert |- ( ( A e. RR* /\ -e A e. RR ) -> A e. RR )

  proof
    cA
    cxr
    wcel
    #
    cA
    cxne
    #
    cr
    wcel
    #
    wa
    @1
    cxne
    #
    cA
    cr
    @0
    @3
    cA
    wceq
    @2
    cA
    xnegneg
    adantr
    @2
    @3
    cr
    wcel
    @0
    @1
    xnegrecl
    adantl
    eqeltrrd
end
