include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "rexr.mm"
include "xnegneg.mm"
include "syl.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cneg.mm"
include "rexneg.mm"
include "renegcl.mm"
include "eqeltrd.mm"
include "xpncan.mm"
include "sylan2.mm"
include "eqtr3d.mm"

theorem xnpcan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR ) -> ( ( A +e -e B ) +e B ) = A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cxne
    #
    cxad
    co
    #
    @3
    cxne
    #
    cxad
    co
    #
    @4
    cB
    cxad
    co
    cA
    @2
    @5
    cB
    @4
    cxad
    @1
    @5
    cB
    wceq
    #
    @0
    @1
    cB
    cxr
    wcel
    @7
    cB
    rexr
    cB
    xnegneg
    syl
    adantl
    oveq2d
    @1
    @0
    @3
    cr
    wcel
    @6
    cA
    wceq
    @1
    @3
    cB
    cneg
    cr
    cB
    rexneg
    cB
    renegcl
    eqeltrd
    cA
    @3
    xpncan
    sylan2
    eqtr3d
end
