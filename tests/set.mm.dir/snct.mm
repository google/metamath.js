include "wcel.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "cdom.mm"
include "ensn1g.mm"
include "c0.mm"
include "csdm.mm"
include "wne.mm"
include "peano1.mm"
include "ne0ii.mm"
include "omex.mm"
include "0sdom.mm"
include "mpbir.mm"
include "0sdom1dom.mm"
include "mpbi.mm"
include "endomtr.mm"
include "sylancl.mm"

theorem snct
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> { A } ~<_ _om )

  proof
    cA
    cV
    wcel
    cA
    csn
    #
    c1o
    cen
    wbr
    c1o
    com
    cdom
    wbr
    #
    @0
    com
    cdom
    wbr
    cA
    cV
    ensn1g
    c0
    com
    csdm
    wbr
    #
    @1
    @2
    com
    c0
    wne
    c0
    com
    peano1
    ne0ii
    com
    omex
    0sdom
    mpbir
    com
    0sdom1dom
    mpbi
    @0
    c1o
    com
    endomtr
    sylancl
end
