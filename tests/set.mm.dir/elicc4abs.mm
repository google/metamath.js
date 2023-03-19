include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "cxr.mm"
include "wb.mm"
include "resubcl.mm"
include "3adant3.mm"
include "rexrd.mm"
include "readdcl.mm"
include "rexr.mm"
include "3ad2ant3.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "absdifle.mm"
include "3coml.mm"
include "bitr4d.mm"

theorem elicc4abs
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( C e. ( ( A - B ) [,] ( A + B ) ) <-> ( abs ` ( C - A ) ) <_ B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cC
    cA
    cB
    cmin
    co
    #
    cA
    cB
    caddc
    co
    #
    cicc
    co
    wcel
    #
    @4
    cC
    cle
    wbr
    cC
    @5
    cle
    wbr
    wa
    #
    cC
    cA
    cmin
    co
    cabs
    cfv
    cB
    cle
    wbr
    #
    @3
    @4
    cxr
    wcel
    @5
    cxr
    wcel
    cC
    cxr
    wcel
    #
    @6
    @7
    wb
    @3
    @4
    @0
    @1
    @4
    cr
    wcel
    @2
    cA
    cB
    resubcl
    3adant3
    rexrd
    @3
    @5
    @0
    @1
    @5
    cr
    wcel
    @2
    cA
    cB
    readdcl
    3adant3
    rexrd
    @2
    @0
    @9
    @1
    cC
    rexr
    3ad2ant3
    @4
    @5
    cC
    elicc4
    syl3anc
    @2
    @0
    @1
    @8
    @7
    wb
    cC
    cA
    cB
    absdifle
    3coml
    bitr4d
end
