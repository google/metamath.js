include "chlt.mm"
include "wcel.mm"
include "cp0.mm"
include "cfv.mm"
include "cv.mm"
include "cplt.mm"
include "wbr.mm"
include "cp1.mm"
include "wa.mm"
include "cbs.mm"
include "wrex.mm"
include "wne.mm"
include "eqid.mm"
include "hlhgt2.mm"
include "cple.mm"
include "wn.mm"
include "wi.mm"
include "simpl.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "op0cl.mm"
include "syl.mm"
include "simpr.mm"
include "hlrelat1.mm"
include "syl3anc.mm"
include "op1cl.mm"
include "mpd3an3.mm"
include "anim12d.mm"
include "reeanv.mm"
include "nbrne2.mm"
include "ad2ant2lr.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem hl2at
  let cA: class A
  let cK: class K
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x
  assume hl2atom.a: |- A = ( Atoms ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint K p
  disjoint K q
  disjoint p x
  disjoint q x
  disjoint A x
  disjoint K x
  assert |- ( K e. HL -> E. p e. A E. q e. A p =/= q )

  proof
    cK
    chlt
    wcel
    #
    cK
    cp0
    cfv
    #
    vx
    cv
    #
    cK
    cplt
    cfv
    #
    wbr
    #
    @2
    cK
    cp1
    cfv
    #
    @3
    wbr
    #
    wa
    #
    vx
    cK
    cbs
    cfv
    #
    wrex
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    vx
    @8
    @3
    @5
    cK
    @1
    @8
    eqid
    #
    @3
    eqid
    #
    @1
    eqid
    #
    @5
    eqid
    #
    hlhgt2
    @0
    @7
    @13
    vx
    @8
    @0
    @2
    @8
    wcel
    #
    wa
    #
    @7
    @9
    @1
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @9
    @2
    @20
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @10
    @2
    @20
    wbr
    wn
    #
    @10
    @5
    @20
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    wa
    #
    @13
    @19
    @4
    @24
    @6
    @28
    @19
    @0
    @1
    @8
    wcel
    #
    @18
    @4
    @24
    wi
    @0
    @18
    simpl
    @19
    cK
    cops
    wcel
    #
    @30
    @0
    @31
    @18
    cK
    hlop
    adantr
    #
    @8
    cK
    @1
    @14
    @16
    op0cl
    syl
    @0
    @18
    simpr
    cA
    @8
    @3
    cK
    @20
    @1
    @2
    vp
    @14
    @20
    eqid
    #
    @15
    hl2atom.a
    hlrelat1
    syl3anc
    @0
    @18
    @5
    @8
    wcel
    #
    @6
    @28
    wi
    @19
    @31
    @34
    @32
    @8
    @5
    cK
    @14
    @17
    op1cl
    syl
    cA
    @8
    @3
    cK
    @20
    @2
    @5
    vq
    @14
    @33
    @15
    hl2atom.a
    hlrelat1
    mpd3an3
    anim12d
    @29
    @23
    @27
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    @13
    @23
    @27
    vp
    vq
    cA
    cA
    reeanv
    @36
    @12
    vp
    cA
    @35
    @11
    vq
    cA
    @22
    @25
    @11
    @21
    @26
    @9
    @10
    @2
    @20
    nbrne2
    ad2ant2lr
    reximi
    reximi
    sylbir
    syl6
    rexlimdva
    mpd
end
