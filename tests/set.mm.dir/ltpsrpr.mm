include "c1p.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cplr.mm"
include "co.mm"
include "cltr.mm"
include "wbr.mm"
include "cltp.mm"
include "cnr.mm"
include "wcel.mm"
include "wb.mm"
include "ltasr.mm"
include "ax-mp.mm"
include "cpp.mm"
include "addcompr.mm"
include "breq1i.mm"
include "ltsrpr.mm"
include "cnp.mm"
include "1pr.mm"
include "ltapr.mm"
include "3bitr4i.mm"
include "bitr3i.mm"

theorem ltpsrpr
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltpsrpr.3: |- C e. R.


  assert |- ( ( C +R [ <. A , 1P >. ] ~R ) <R ( C +R [ <. B , 1P >. ] ~R ) <-> A <P B )

  proof
    cC
    cA
    c1p
    cop
    cer
    cec
    #
    cplr
    co
    cC
    cB
    c1p
    cop
    cer
    cec
    #
    cplr
    co
    cltr
    wbr
    #
    @0
    @1
    cltr
    wbr
    #
    cA
    cB
    cltp
    wbr
    #
    cC
    cnr
    wcel
    @3
    @2
    wb
    ltpsrpr.3
    @0
    @1
    cC
    ltasr
    ax-mp
    cA
    c1p
    cpp
    co
    #
    c1p
    cB
    cpp
    co
    #
    cltp
    wbr
    c1p
    cA
    cpp
    co
    #
    @6
    cltp
    wbr
    #
    @3
    @4
    @5
    @7
    @6
    cltp
    cA
    c1p
    addcompr
    breq1i
    cA
    c1p
    cB
    c1p
    ltsrpr
    c1p
    cnp
    wcel
    @4
    @8
    wb
    1pr
    cA
    cB
    c1p
    ltapr
    ax-mp
    3bitr4i
    bitr3i
end
