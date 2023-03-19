include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "csdm.mm"
include "cen.mm"
include "com.mm"
include "1onn.mm"
include "a1i.mm"
include "cdadom3.mm"
include "sylan2.mm"
include "simpr.mm"
include "wb.mm"
include "nnfi.mm"
include "mp1i.mm"
include "fidomtri2.mm"
include "wi.mm"
include "domfi.mm"
include "ex.mm"
include "syl.mm"
include "sylbird.mm"
include "mt3d.mm"
include "canthp1.mm"
include "jca.mm"
include "gchen1.mm"
include "mpdan.mm"
include "ensymd.mm"

theorem gchcda1
  let cA: class A


  assert |- ( ( A e. GCH /\ -. A e. Fin ) -> ( A +c 1o ) ~~ A )

  proof
    cA
    cgch
    wcel
    #
    cA
    cfn
    wcel
    #
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
    @3
    cA
    @4
    cdom
    wbr
    #
    @4
    cA
    cpw
    csdm
    wbr
    #
    wa
    cA
    @4
    cen
    wbr
    @3
    @5
    @6
    @2
    @0
    c1o
    com
    wcel
    #
    @5
    @7
    @2
    1onn
    a1i
    cA
    c1o
    cgch
    com
    cdadom3
    sylan2
    @3
    c1o
    cA
    csdm
    wbr
    #
    @6
    @3
    @8
    @1
    @0
    @2
    simpr
    @3
    @8
    wn
    #
    cA
    c1o
    cdom
    wbr
    #
    @1
    @2
    @0
    c1o
    cfn
    wcel
    #
    @10
    @9
    wb
    @7
    @11
    @2
    1onn
    c1o
    nnfi
    #
    mp1i
    cA
    c1o
    cgch
    fidomtri2
    sylan2
    @3
    @11
    @10
    @1
    wi
    @7
    @11
    @3
    1onn
    @12
    mp1i
    @11
    @10
    @1
    c1o
    cA
    domfi
    ex
    syl
    sylbird
    mt3d
    cA
    canthp1
    syl
    jca
    cA
    @4
    gchen1
    mpdan
    ensymd
end
