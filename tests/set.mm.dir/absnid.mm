include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "le0neg1.mm"
include "wa.mm"
include "cc.mm"
include "recn.mm"
include "absneg.mm"
include "syl.mm"
include "adantr.mm"
include "renegcl.mm"
include "absid.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"

theorem absnid
  let cA: class A


  assert |- ( ( A e. RR /\ A <_ 0 ) -> ( abs ` A ) = -u A )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    cle
    wbr
    #
    cA
    cabs
    cfv
    #
    cA
    cneg
    #
    wceq
    #
    @0
    @1
    cc0
    @3
    cle
    wbr
    #
    @4
    cA
    le0neg1
    @0
    @5
    @4
    @0
    @5
    wa
    @3
    cabs
    cfv
    #
    @2
    @3
    @0
    @6
    @2
    wceq
    #
    @5
    @0
    cA
    cc
    wcel
    @7
    cA
    recn
    cA
    absneg
    syl
    adantr
    @0
    @3
    cr
    wcel
    @5
    @6
    @3
    wceq
    cA
    renegcl
    @3
    absid
    sylan
    eqtr3d
    ex
    sylbid
    imp
end
