include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "cmd.mm"
include "wi.mm"
include "choccl.mm"
include "cvmd.mm"
include "3expia.mm"
include "syl2an.mm"
include "wb.mm"
include "simpr.mm"
include "chjcl.mm"
include "cvcon3.mm"
include "syl2anc.mm"
include "chdmj1.mm"
include "breq1d.mm"
include "bitrd.mm"
include "dmdmd.mm"
include "3imtr4d.mm"
include "3impia.mm"

theorem cvdmd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ B <oH ( A vH B ) ) -> A MH* B )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cB
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    cA
    cB
    cdmd
    wbr
    #
    @0
    @1
    wa
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cin
    #
    @7
    ccv
    wbr
    #
    @6
    @7
    cmd
    wbr
    #
    @3
    @4
    @0
    @6
    cch
    wcel
    #
    @7
    cch
    wcel
    #
    @9
    @10
    wi
    @1
    cA
    choccl
    cB
    choccl
    @11
    @12
    @9
    @10
    @6
    @7
    cvmd
    3expia
    syl2an
    @5
    @3
    @2
    cort
    cfv
    #
    @7
    ccv
    wbr
    #
    @9
    @5
    @1
    @2
    cch
    wcel
    @3
    @14
    wb
    @0
    @1
    simpr
    cA
    cB
    chjcl
    cB
    @2
    cvcon3
    syl2anc
    @5
    @13
    @8
    @7
    ccv
    cA
    cB
    chdmj1
    breq1d
    bitrd
    cA
    cB
    dmdmd
    3imtr4d
    3impia
end
