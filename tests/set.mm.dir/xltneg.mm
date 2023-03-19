include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cxne.mm"
include "xltnegi.mm"
include "3expia.mm"
include "wi.mm"
include "xnegcl.mm"
include "syl2anr.mm"
include "xnegneg.mm"
include "breqan12d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem xltneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> -e B < -e A ) )

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
    cA
    cB
    clt
    wbr
    #
    cB
    cxne
    #
    cA
    cxne
    #
    clt
    wbr
    #
    @0
    @1
    @3
    @6
    cA
    cB
    xltnegi
    3expia
    @2
    @6
    @5
    cxne
    #
    @4
    cxne
    #
    clt
    wbr
    #
    @3
    @1
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @6
    @9
    wi
    @0
    cB
    xnegcl
    cA
    xnegcl
    @10
    @11
    @6
    @9
    @4
    @5
    xltnegi
    3expia
    syl2anr
    @0
    @1
    @7
    cA
    @8
    cB
    clt
    cA
    xnegneg
    cB
    xnegneg
    breqan12d
    sylibd
    impbid
end
