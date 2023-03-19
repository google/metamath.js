include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cdom.mm"
include "domnsym.mm"
include "con2i.mm"
include "0sdom1dom.mm"
include "sylnibr.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "necon2bbid.mm"
include "syl.mm"
include "mpbird.mm"
include "wne.mm"
include "1n0.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "0sdom.mm"
include "mpbir.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem sdom1
  let cA: class A


  assert |- ( A ~< 1o <-> A = (/) )

  proof
    cA
    c1o
    csdm
    wbr
    #
    cA
    c0
    wceq
    #
    @0
    @1
    c0
    cA
    csdm
    wbr
    #
    wn
    #
    @0
    c1o
    cA
    cdom
    wbr
    #
    @2
    @4
    @0
    c1o
    cA
    domnsym
    con2i
    cA
    0sdom1dom
    sylnibr
    @0
    cA
    cvv
    wcel
    #
    @1
    @3
    wb
    cA
    c1o
    csdm
    relsdom
    brrelexi
    @5
    @2
    cA
    c0
    cA
    cvv
    0sdomg
    necon2bbid
    syl
    mpbird
    @1
    @0
    c0
    c1o
    csdm
    wbr
    #
    @6
    c1o
    c0
    wne
    1n0
    c1o
    c1o
    con0
    1on
    elexi
    0sdom
    mpbir
    cA
    c0
    c1o
    csdm
    breq1
    mpbiri
    impbii
end
