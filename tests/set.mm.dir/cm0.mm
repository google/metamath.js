include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "h0elch.mm"
include "choccli.mm"
include "chjcl.mm"
include "mpan.mm"
include "chm0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "incom.mm"
include "3eqtr4g.mm"
include "wb.mm"
include "cmbr3.mm"
include "mpbird.mm"

theorem cm0
  let cA: class A


  assert |- ( A e. CH -> 0H C_H A )

  proof
    cA
    cch
    wcel
    #
    c0h
    cA
    ccm
    wbr
    #
    c0h
    c0h
    cort
    cfv
    #
    cA
    chj
    co
    #
    cin
    #
    c0h
    cA
    cin
    #
    wceq
    #
    @0
    @3
    c0h
    cin
    #
    cA
    c0h
    cin
    #
    @4
    @5
    @0
    @7
    c0h
    @8
    @0
    @3
    cch
    wcel
    #
    @7
    c0h
    wceq
    @2
    cch
    wcel
    @0
    @9
    c0h
    h0elch
    choccli
    @2
    cA
    chjcl
    mpan
    @3
    chm0
    syl
    cA
    chm0
    eqtr4d
    c0h
    @3
    incom
    c0h
    cA
    incom
    3eqtr4g
    c0h
    cch
    wcel
    @0
    @1
    @6
    wb
    h0elch
    c0h
    cA
    cmbr3
    mpan
    mpbird
end
