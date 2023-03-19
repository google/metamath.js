include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "csuc.mm"
include "cdom.mm"
include "c1o.mm"
include "com.mm"
include "wcel.mm"
include "wb.mm"
include "peano1.mm"
include "sucdom.mm"
include "ax-mp.mm"
include "df-1o.mm"
include "breq1i.mm"
include "bitr4i.mm"

theorem 0sdom1dom
  let cA: class A


  assert |- ( (/) ~< A <-> 1o ~<_ A )

  proof
    c0
    cA
    csdm
    wbr
    #
    c0
    csuc
    #
    cA
    cdom
    wbr
    #
    c1o
    cA
    cdom
    wbr
    c0
    com
    wcel
    @0
    @2
    wb
    peano1
    c0
    cA
    sucdom
    ax-mp
    c1o
    @1
    cA
    cdom
    df-1o
    breq1i
    bitr4i
end
