include "cfin3.mm"
include "wcel.mm"
include "cfin4.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wn.mm"
include "cpw.mm"
include "isfin3.mm"
include "isfin4-2.mm"
include "ibi.mm"
include "csdm.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "canth2g.mm"
include "syl.mm"
include "domsdomtr.mm"
include "mpdan.mm"
include "sdomdom.mm"
include "nsyl.mm"
include "sylbi.mm"
include "mpbird.mm"

theorem fin34
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin3 -> A e. Fin4 )

  proof
    cA
    cfin3
    wcel
    #
    cA
    cfin4
    wcel
    com
    cA
    cdom
    wbr
    #
    wn
    #
    @0
    cA
    cpw
    #
    cfin4
    wcel
    #
    @2
    cA
    isfin3
    @4
    com
    @3
    cdom
    wbr
    #
    @1
    @4
    @5
    wn
    @3
    cfin4
    isfin4-2
    ibi
    @1
    com
    @3
    csdm
    wbr
    #
    @5
    @1
    cA
    @3
    csdm
    wbr
    #
    @6
    @1
    cA
    cvv
    wcel
    @7
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    cvv
    canth2g
    syl
    com
    cA
    @3
    domsdomtr
    mpdan
    com
    @3
    sdomdom
    syl
    nsyl
    sylbi
    cA
    cfin3
    isfin4-2
    mpbird
end
