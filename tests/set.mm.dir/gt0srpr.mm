include "c1p.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cltr.mm"
include "wbr.mm"
include "cpp.mm"
include "co.mm"
include "cltp.mm"
include "c0r.mm"
include "ltsrpr.mm"
include "df-0r.mm"
include "breq1i.mm"
include "cnp.mm"
include "wcel.mm"
include "wb.mm"
include "1pr.mm"
include "ltapr.mm"
include "ax-mp.mm"
include "3bitr4i.mm"

theorem gt0srpr
  let cA: class A
  let cB: class B


  assert |- ( 0R <R [ <. A , B >. ] ~R <-> B <P A )

  proof
    c1p
    c1p
    cop
    cer
    cec
    #
    cA
    cB
    cop
    cer
    cec
    #
    cltr
    wbr
    c1p
    cB
    cpp
    co
    c1p
    cA
    cpp
    co
    cltp
    wbr
    #
    c0r
    @1
    cltr
    wbr
    cB
    cA
    cltp
    wbr
    #
    c1p
    c1p
    cA
    cB
    ltsrpr
    c0r
    @0
    @1
    cltr
    df-0r
    breq1i
    c1p
    cnp
    wcel
    @3
    @2
    wb
    1pr
    cB
    cA
    c1p
    ltapr
    ax-mp
    3bitr4i
end
