include "csn.mm"
include "c0.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cop.mm"
include "0ex.mm"
include "f1osn.mm"
include "snex.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "ax-mp.mm"
include "bren.mm"
include "mpbir.mm"
include "df1o2.mm"
include "breqtrri.mm"

theorem ensn1
  let cA: class A
  let vf: setvar f
  assume ensn1.1: |- A e. _V


  assert |- { A } ~~ 1o

  proof
    cA
    csn
    #
    c0
    csn
    #
    c1o
    cen
    @0
    @1
    cen
    wbr
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @0
    @1
    cA
    c0
    cop
    #
    csn
    #
    wf1o
    #
    @4
    cA
    c0
    ensn1.1
    0ex
    f1osn
    @3
    @7
    vf
    @6
    @5
    snex
    @0
    @1
    @2
    @6
    f1oeq1
    spcev
    ax-mp
    @0
    @1
    vf
    bren
    mpbir
    df1o2
    breqtrri
end
