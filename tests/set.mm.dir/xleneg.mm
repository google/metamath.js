include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cxne.mm"
include "cle.mm"
include "wb.mm"
include "xltneg.mm"
include "ancoms.mm"
include "notbid.mm"
include "xrlenlt.mm"
include "xnegcl.mm"
include "syl2anr.mm"
include "3bitr4d.mm"

theorem xleneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B <-> -e B <_ -e A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cB
    cA
    clt
    wbr
    #
    wn
    cA
    cxne
    #
    cB
    cxne
    #
    clt
    wbr
    #
    wn
    #
    cA
    cB
    cle
    wbr
    @5
    @4
    cle
    wbr
    #
    @2
    @3
    @6
    @1
    @0
    @3
    @6
    wb
    cB
    cA
    xltneg
    ancoms
    notbid
    cA
    cB
    xrlenlt
    @1
    @5
    cxr
    wcel
    @4
    cxr
    wcel
    @8
    @7
    wb
    @0
    cB
    xnegcl
    cA
    xnegcl
    @5
    @4
    xrlenlt
    syl2anr
    3bitr4d
end
