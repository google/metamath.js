include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csdm.mm"
include "cn.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "simpr.mm"
include "wb.mm"
include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "reldom.mm"
include "a1i.mm"
include "brrelex.mm"
include "mpancom.mm"
include "0sdomg.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "cen.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "mpdan.mm"
include "fodomr.mm"
include "syl2anc.mm"

theorem nnfoctb
  let cA: class A
  let vf: setvar f

  disjoint A f
  assert |- ( ( A ~<_ _om /\ A =/= (/) ) -> E. f f : NN -onto-> A )

  proof
    cA
    com
    cdom
    wbr
    #
    cA
    c0
    wne
    #
    wa
    #
    c0
    cA
    csdm
    wbr
    #
    cA
    cn
    cdom
    wbr
    #
    cn
    cA
    vf
    cv
    wfo
    vf
    wex
    @2
    @3
    @1
    @0
    @1
    simpr
    @0
    @3
    @1
    wb
    #
    @1
    @0
    cA
    cvv
    wcel
    #
    @5
    cdom
    wrel
    #
    @0
    @6
    @7
    @0
    reldom
    a1i
    cA
    com
    cdom
    brrelex
    mpancom
    cA
    cvv
    0sdomg
    syl
    adantr
    mpbird
    @0
    @4
    @1
    @0
    com
    cn
    cen
    wbr
    #
    @4
    @8
    @0
    cn
    com
    nnenom
    ensymi
    a1i
    cA
    com
    cn
    domentr
    mpdan
    adantr
    cn
    cA
    vf
    fodomr
    syl2anc
end
