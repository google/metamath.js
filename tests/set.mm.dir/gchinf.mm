include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "cdom.mm"
include "gchcda1.mm"
include "ensymd.mm"
include "cfin4.mm"
include "wb.mm"
include "isfin4-2.mm"
include "adantr.mm"
include "csdm.mm"
include "isfin4-3.mm"
include "sdomnen.mm"
include "sylbi.mm"
include "syl6bir.mm"
include "mt4d.mm"

theorem gchinf
  let cA: class A


  assert |- ( ( A e. GCH /\ -. A e. Fin ) -> _om ~<_ A )

  proof
    cA
    cgch
    wcel
    #
    cA
    cfn
    wcel
    wn
    #
    wa
    #
    cA
    cA
    c1o
    ccda
    co
    #
    cen
    wbr
    #
    com
    cA
    cdom
    wbr
    #
    @2
    @3
    cA
    cA
    gchcda1
    ensymd
    @2
    @5
    wn
    #
    cA
    cfin4
    wcel
    #
    @4
    wn
    #
    @0
    @7
    @6
    wb
    @1
    cA
    cgch
    isfin4-2
    adantr
    @7
    cA
    @3
    csdm
    wbr
    @8
    cA
    isfin4-3
    cA
    @3
    sdomnen
    sylbi
    syl6bir
    mt4d
end
