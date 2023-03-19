include "cfrgr.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "w3a.mm"
include "wrex.mm"
include "wral.mm"
include "ccycls.mm"
include "c3.mm"
include "wceq.mm"
include "cc0.mm"
include "wex.mm"
include "eqid.mm"
include "3cyclfrgrrn.mm"
include "cumgr.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgrumgr.mm"
include "syl.mm"
include "ad4antr.mm"
include "simpr.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "adantr.mm"
include "umgr3cyclex.mm"
include "syl3anc.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "ralimdva.mm"
include "mpd.mm"

theorem 3cyclfrgr
  let vv: setvar v
  let vf: setvar f
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vb: setvar b
  let vc: setvar c
  assume 3cyclfrgr.v: |- V = ( Vtx ` G )

  disjoint G f
  disjoint G p
  disjoint G v
  disjoint f p
  disjoint f v
  disjoint p v
  disjoint V v
  disjoint G b
  disjoint G c
  disjoint b c
  disjoint b f
  disjoint b p
  disjoint b v
  disjoint c f
  disjoint c p
  disjoint c v
  disjoint V b
  disjoint V c
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` V ) ) -> A. v e. V E. f E. p ( f ( Cycles ` G ) p /\ ( # ` f ) = 3 /\ ( p ` 0 ) = v ) )

  proof
    cG
    cfrgr
    wcel
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    wa
    #
    vv
    cv
    #
    vb
    cv
    #
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @4
    vc
    cv
    #
    cpr
    @5
    wcel
    @6
    @3
    cpr
    @5
    wcel
    w3a
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    vv
    cV
    wral
    vf
    cv
    #
    vp
    cv
    #
    cG
    ccycls
    cfv
    wbr
    @9
    chash
    cfv
    c3
    wceq
    cc0
    @10
    cfv
    @3
    wceq
    w3a
    vp
    wex
    vf
    wex
    #
    vv
    cV
    wral
    @5
    cG
    cV
    vv
    vb
    vc
    3cyclfrgr.v
    @5
    eqid
    #
    3cyclfrgrrn
    @2
    @8
    @11
    vv
    cV
    @2
    @3
    cV
    wcel
    #
    wa
    #
    @7
    @11
    vb
    vc
    cV
    cV
    @14
    @4
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    wa
    #
    @7
    @11
    @18
    @7
    wa
    cG
    cumgr
    wcel
    #
    @13
    @15
    @16
    w3a
    #
    @7
    @11
    @0
    @19
    @1
    @13
    @17
    @7
    @0
    cG
    cusgr
    wcel
    @19
    cG
    frgrusgr
    cG
    usgrumgr
    syl
    ad4antr
    @18
    @20
    @7
    @18
    @13
    @17
    wa
    @20
    @14
    @13
    @17
    @2
    @13
    simpr
    anim1i
    @13
    @15
    @16
    3anass
    sylibr
    adantr
    @18
    @7
    simpr
    @3
    @4
    @6
    vf
    @5
    cG
    cV
    vp
    3cyclfrgr.v
    @12
    umgr3cyclex
    syl3anc
    ex
    rexlimdvva
    ralimdva
    mpd
end
