include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "clt.mm"
include "csup.mm"
include "w3a.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wor.mm"
include "zssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1.mm"
include "fisup2g.mm"
include "syl13anc.mm"
include "id.mm"
include "syl6ss.mm"
include "3ad2ant1.mm"
include "ssrexv.mm"
include "syl.mm"
include "ssel2.mm"
include "zred.mm"
include "ex.mm"
include "adantr.mm"
include "imp.mm"
include "simplr.mm"
include "lenltd.mm"
include "bicomd.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "adantrd.mm"
include "reximdva.mm"
include "syld.mm"
include "mpd.mm"
include "suprzcl.mm"
include "syld3an3.mm"

theorem suprfinzcl
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vr: setvar r


  assert |- ( ( A C_ ZZ /\ A =/= (/) /\ A e. Fin ) -> sup ( A , RR , < ) e. A )

  proof
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    va
    cv
    #
    vr
    cv
    #
    cle
    wbr
    #
    va
    cA
    wral
    #
    vr
    cr
    wrex
    #
    cA
    cr
    clt
    csup
    cA
    wcel
    @0
    @1
    @2
    w3a
    #
    @4
    @3
    clt
    wbr
    wn
    #
    va
    cA
    wral
    #
    @3
    @4
    clt
    wbr
    @3
    vb
    cv
    clt
    wbr
    vb
    cA
    wrex
    wi
    va
    cz
    wral
    #
    wa
    #
    vr
    cA
    wrex
    #
    @7
    @8
    cz
    clt
    wor
    #
    @2
    @1
    @0
    @13
    @14
    @8
    cz
    cr
    wss
    cr
    clt
    wor
    @14
    zssre
    ltso
    cz
    cr
    clt
    soss
    mp2
    a1i
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp1
    vr
    va
    vb
    cz
    cA
    clt
    fisup2g
    syl13anc
    @8
    @13
    @12
    vr
    cr
    wrex
    #
    @7
    @8
    cA
    cr
    wss
    #
    @13
    @15
    wi
    @0
    @1
    @16
    @2
    @0
    cA
    cz
    cr
    @0
    id
    zssre
    syl6ss
    3ad2ant1
    @12
    vr
    cA
    cr
    ssrexv
    syl
    @8
    @12
    @6
    vr
    cr
    @8
    @4
    cr
    wcel
    #
    wa
    #
    @10
    @6
    @11
    @18
    @10
    @6
    @18
    @9
    @5
    va
    cA
    @18
    @3
    cA
    wcel
    #
    wa
    #
    @5
    @9
    @20
    @3
    @4
    @18
    @19
    @3
    cr
    wcel
    #
    @8
    @19
    @21
    wi
    #
    @17
    @0
    @1
    @22
    @2
    @0
    @19
    @21
    @0
    @19
    wa
    @3
    cA
    cz
    @3
    ssel2
    zred
    ex
    3ad2ant1
    adantr
    imp
    @8
    @17
    @19
    simplr
    lenltd
    bicomd
    ralbidva
    biimpd
    adantrd
    reximdva
    syld
    mpd
    vr
    va
    cA
    suprzcl
    syld3an3
end
