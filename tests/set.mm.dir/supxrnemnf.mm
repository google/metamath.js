include "cxr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cmnf.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "supxrcl.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simp1.mm"
include "jctir.mm"
include "wceq.mm"
include "simpl.mm"
include "sselda.mm"
include "simpr.mm"
include "simplr.mm"
include "nelneq.mm"
include "syl2anc.mm"
include "ngtmnft.mm"
include "biimprd.mm"
include "con1d.mm"
include "sylc.mm"
include "reximdva0.mm"
include "3impa.mm"
include "3com23.mm"
include "supxrlub.mm"
include "xrltne.mm"
include "syl3anc.mm"

theorem supxrnemnf
  let cA: class A
  let vx: setvar x


  assert |- ( ( A C_ RR* /\ A =/= (/) /\ -. -oo e. A ) -> sup ( A , RR* , < ) =/= -oo )

  proof
    cA
    cxr
    wss
    #
    cA
    c0
    wne
    #
    cmnf
    cA
    wcel
    wn
    #
    w3a
    #
    cmnf
    cxr
    wcel
    #
    cA
    cxr
    clt
    csup
    #
    cxr
    wcel
    #
    cmnf
    @5
    clt
    wbr
    #
    @5
    cmnf
    wne
    @4
    @3
    mnfxr
    a1i
    @0
    @1
    @6
    @2
    cA
    supxrcl
    3ad2ant1
    @3
    @0
    @4
    wa
    #
    cmnf
    vx
    cv
    #
    clt
    wbr
    #
    vx
    cA
    wrex
    #
    @7
    @3
    @0
    @4
    @0
    @1
    @2
    simp1
    mnfxr
    jctir
    @0
    @2
    @1
    @11
    @0
    @2
    @1
    @11
    @0
    @2
    wa
    #
    @10
    vx
    cA
    @12
    @9
    cA
    wcel
    #
    wa
    #
    @9
    cxr
    wcel
    #
    @9
    cmnf
    wceq
    #
    wn
    #
    @10
    @12
    cA
    cxr
    @9
    @0
    @2
    simpl
    sselda
    @14
    @13
    @2
    @17
    @12
    @13
    simpr
    @0
    @2
    @13
    simplr
    @9
    cmnf
    cA
    nelneq
    syl2anc
    @15
    @10
    @16
    @15
    @16
    @10
    wn
    @9
    ngtmnft
    biimprd
    con1d
    sylc
    reximdva0
    3impa
    3com23
    @8
    @7
    @11
    vx
    cA
    cmnf
    supxrlub
    biimprd
    sylc
    cmnf
    @5
    xrltne
    syl3anc
end
