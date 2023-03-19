include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "csdm.mm"
include "cen.mm"
include "simpl.mm"
include "cdadom3.mm"
include "syl2anc.mm"
include "canth2g.mm"
include "adantr.mm"
include "sdomdom.mm"
include "syl.mm"
include "cdadom1.mm"
include "cdadom2.mm"
include "domtr.mm"
include "c1o.mm"
include "pwcda1.mm"
include "gchcda1.mm"
include "pwen.mm"
include "entr.mm"
include "domentr.mm"
include "com.mm"
include "gchinf.mm"
include "pwcdandom.mm"
include "ensym.mm"
include "endom.mm"
include "nsyl.mm"
include "brsdom.mm"
include "sylanbrc.mm"
include "jca.mm"
include "gchen1.mm"
include "mpdan.mm"
include "ensymd.mm"

theorem gchcdaidm
  let cA: class A


  assert |- ( ( A e. GCH /\ -. A e. Fin ) -> ( A +c A ) ~~ A )

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
    cA
    ccda
    co
    #
    @2
    cA
    @3
    cdom
    wbr
    #
    @3
    cA
    cpw
    #
    csdm
    wbr
    #
    wa
    cA
    @3
    cen
    wbr
    @2
    @4
    @6
    @2
    @0
    @0
    @4
    @0
    @1
    simpl
    #
    @7
    cA
    cA
    cgch
    cgch
    cdadom3
    syl2anc
    @2
    @3
    @5
    cdom
    wbr
    #
    @3
    @5
    cen
    wbr
    #
    wn
    @6
    @2
    @3
    @5
    @5
    ccda
    co
    #
    cdom
    wbr
    #
    @10
    @5
    cen
    wbr
    #
    @8
    @2
    cA
    @5
    cdom
    wbr
    #
    @11
    @2
    cA
    @5
    csdm
    wbr
    #
    @13
    @0
    @14
    @1
    cA
    cgch
    canth2g
    adantr
    cA
    @5
    sdomdom
    syl
    @13
    @3
    @5
    cA
    ccda
    co
    #
    cdom
    wbr
    @15
    @10
    cdom
    wbr
    @11
    cA
    @5
    cA
    cdadom1
    cA
    @5
    @5
    cdadom2
    @3
    @15
    @10
    domtr
    syl2anc
    syl
    @2
    @10
    cA
    c1o
    ccda
    co
    #
    cpw
    #
    cen
    wbr
    #
    @17
    @5
    cen
    wbr
    #
    @12
    @0
    @18
    @1
    cA
    cgch
    pwcda1
    adantr
    @2
    @16
    cA
    cen
    wbr
    @19
    cA
    gchcda1
    @16
    cA
    pwen
    syl
    @10
    @17
    @5
    entr
    syl2anc
    @3
    @10
    @5
    domentr
    syl2anc
    @2
    @5
    @3
    cdom
    wbr
    #
    @9
    @2
    com
    cA
    cdom
    wbr
    @20
    wn
    cA
    gchinf
    cA
    pwcdandom
    syl
    @9
    @5
    @3
    cen
    wbr
    @20
    @3
    @5
    ensym
    @5
    @3
    endom
    syl
    nsyl
    @3
    @5
    brsdom
    sylanbrc
    jca
    cA
    @3
    gchen1
    mpdan
    ensymd
end
