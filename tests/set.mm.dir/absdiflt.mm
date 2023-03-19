include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "caddc.mm"
include "wb.mm"
include "resubcl.mm"
include "abslt.mm"
include "stoic3.mm"
include "renegcl.mm"
include "ltaddsub2.mm"
include "syl3an2.mm"
include "3comr.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "negsub.mm"
include "syl2an.mm"
include "3adant1.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "ltsubadd2.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem absdiflt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( abs ` ( A - B ) ) < C <-> ( ( B - C ) < A /\ A < ( B + C ) ) ) )

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
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    cC
    clt
    wbr
    #
    cC
    cneg
    #
    @4
    clt
    wbr
    #
    @4
    cC
    clt
    wbr
    #
    wa
    #
    cB
    cC
    cmin
    co
    #
    cA
    clt
    wbr
    #
    cA
    cB
    cC
    caddc
    co
    clt
    wbr
    #
    wa
    @0
    @1
    @4
    cr
    wcel
    @2
    @5
    @9
    wb
    cA
    cB
    resubcl
    @4
    cC
    abslt
    stoic3
    @3
    @7
    @11
    @8
    @12
    @3
    cB
    @6
    caddc
    co
    #
    cA
    clt
    wbr
    #
    @7
    @11
    @1
    @2
    @0
    @14
    @7
    wb
    #
    @2
    @1
    @6
    cr
    wcel
    @0
    @15
    cC
    renegcl
    cB
    @6
    cA
    ltaddsub2
    syl3an2
    3comr
    @3
    @13
    @10
    cA
    clt
    @1
    @2
    @13
    @10
    wceq
    #
    @0
    @1
    cB
    cc
    wcel
    cC
    cc
    wcel
    @16
    @2
    cB
    recn
    cC
    recn
    cB
    cC
    negsub
    syl2an
    3adant1
    breq1d
    bitr3d
    cA
    cB
    cC
    ltsubadd2
    anbi12d
    bitrd
end
