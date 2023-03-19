include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c3.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "crusgr.mm"
include "wn.mm"
include "cn0.mm"
include "wa.mm"
include "wi.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "simp2.mm"
include "hashcl.mm"
include "cc0.mm"
include "cr.mm"
include "0red.mm"
include "3re.mm"
include "a1i.mm"
include "nn0re.mm"
include "3jca.mm"
include "adantr.mm"
include "3pos.mm"
include "simpr.mm"
include "lttr.mm"
include "imp.mm"
include "syl12anc.mm"
include "ex.mm"
include "ltne.mm"
include "syl6an.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "biimpcd.mm"
include "syl6.mm"
include "com23.mm"
include "mpcom.mm"
include "3imp.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "frgrregord13.mm"
include "syl2anc.mm"
include "1red.mm"
include "1lt3.mm"
include "lttrd.mm"
include "gtned.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "sylan.mm"
include "jaod.mm"
include "syl.mm"
include "mpd.mm"
include "ax-1.mm"
include "pm2.61i.mm"
include "ralrimiva.mm"

theorem frgrogt3nreg
  let vk: setvar k
  let cG: class G
  let cV: class V
  let vp: setvar p
  let cK: class K
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  assume frgrreggt1.v: |- V = ( Vtx ` G )

  disjoint G k
  disjoint V k
  disjoint G p
  disjoint K p
  disjoint V p
  disjoint G v
  disjoint K v
  disjoint V v
  disjoint G a
  disjoint G b
  disjoint a b
  disjoint K a
  disjoint K b
  disjoint V a
  disjoint V b
  assert |- ( ( G e. FriendGraph /\ V e. Fin /\ 3 < ( # ` V ) ) -> A. k e. NN0 -. G RegUSGraph k )

  proof
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    c3
    cV
    chash
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    cG
    vk
    cv
    #
    crusgr
    wbr
    #
    wn
    #
    vk
    cn0
    @6
    @4
    @5
    cn0
    wcel
    #
    wa
    #
    @7
    wi
    @6
    @9
    @7
    @6
    @9
    wa
    #
    @2
    c1
    wceq
    #
    @2
    c3
    wceq
    #
    wo
    #
    @7
    @10
    @0
    @1
    cV
    c0
    wne
    #
    w3a
    #
    @6
    @13
    @4
    @15
    @6
    @8
    @4
    @0
    @1
    @14
    @0
    @1
    @3
    simp1
    @0
    @1
    @3
    simp2
    @0
    @1
    @3
    @14
    @1
    @3
    @14
    wi
    #
    wi
    @0
    @2
    cn0
    wcel
    #
    @1
    @16
    cV
    hashcl
    #
    @17
    @3
    @1
    @14
    @17
    @3
    @2
    cc0
    wne
    #
    @1
    @14
    wi
    @17
    cc0
    cr
    wcel
    #
    @3
    cc0
    @2
    clt
    wbr
    #
    @19
    @17
    0red
    #
    @17
    @3
    @21
    @17
    @3
    wa
    #
    @20
    c3
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    w3a
    #
    cc0
    c3
    clt
    wbr
    #
    @3
    @21
    @17
    @26
    @3
    @17
    @20
    @24
    @25
    @22
    @24
    @17
    3re
    a1i
    #
    @2
    nn0re
    #
    3jca
    adantr
    @27
    @23
    3pos
    a1i
    @17
    @3
    simpr
    #
    @26
    @27
    @3
    wa
    @21
    cc0
    c3
    @2
    lttr
    imp
    syl12anc
    ex
    cc0
    @2
    ltne
    syl6an
    @1
    @19
    @14
    @1
    @2
    cc0
    cV
    c0
    cV
    cfn
    hasheq0
    necon3bid
    biimpcd
    syl6
    com23
    mpcom
    a1i
    3imp
    3jca
    ad2antrl
    @6
    @9
    simpl
    cG
    @5
    cV
    frgrreggt1.v
    frgrregord13
    syl2anc
    @4
    @13
    @7
    wi
    #
    @6
    @8
    @0
    @1
    @3
    @31
    @1
    @3
    @31
    wi
    #
    wi
    @0
    @1
    @17
    @32
    @18
    @17
    @3
    @31
    @23
    @11
    @7
    @12
    @23
    @2
    c1
    wne
    @11
    @7
    @23
    c1
    @2
    @23
    1red
    #
    @23
    c1
    c3
    @2
    @33
    @24
    @23
    3re
    a1i
    @17
    @25
    @3
    @29
    adantr
    c1
    c3
    clt
    wbr
    @23
    1lt3
    a1i
    @30
    lttrd
    gtned
    @7
    @2
    c1
    eqneqall
    syl5com
    @23
    @2
    c3
    wne
    #
    @12
    @7
    @17
    @24
    @3
    @34
    @28
    c3
    @2
    ltne
    sylan
    @7
    @2
    c3
    eqneqall
    syl5com
    jaod
    ex
    syl
    a1i
    3imp
    ad2antrl
    mpd
    ex
    @7
    @9
    ax-1
    pm2.61i
    ralrimiva
end
