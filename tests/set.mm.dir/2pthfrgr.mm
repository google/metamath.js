include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cspthson.mm"
include "co.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wex.mm"
include "eqid.mm"
include "2pthfrgrrn2.mm"
include "cuhgr.mm"
include "w3a.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgruhgr.mm"
include "syl.mm"
include "adantr.mm"
include "simpllr.mm"
include "simpr.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "3jca.mm"
include "jca.mm"
include "simprrl.mm"
include "eldifsn.mm"
include "necom.mm"
include "biimpi.mm"
include "simplbiim.mm"
include "ad3antlr.mm"
include "simprrr.mm"
include "simprl.mm"
include "2pthon3v.mm"
include "syl131anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "mpd.mm"

theorem 2pthfrgr
  let vf: setvar f
  let cG: class G
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  assume 2pthfrgr.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G p
  disjoint a b
  disjoint a f
  disjoint a p
  disjoint b f
  disjoint b p
  disjoint f p
  disjoint V a
  disjoint V b
  disjoint G m
  disjoint a m
  disjoint b m
  disjoint f m
  disjoint m p
  disjoint V m
  assert |- ( G e. FriendGraph -> A. a e. V A. b e. ( V \ { a } ) E. f E. p ( f ( a ( SPathsOn ` G ) b ) p /\ ( # ` f ) = 2 ) )

  proof
    cG
    cfrgr
    wcel
    #
    va
    cv
    #
    vm
    cv
    #
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @2
    vb
    cv
    #
    cpr
    @3
    wcel
    wa
    #
    @1
    @2
    wne
    #
    @2
    @4
    wne
    #
    wa
    #
    wa
    #
    vm
    cV
    wrex
    #
    vb
    cV
    @1
    csn
    #
    cdif
    #
    wral
    #
    va
    cV
    wral
    vf
    cv
    #
    vp
    cv
    @1
    @4
    cG
    cspthson
    cfv
    co
    wbr
    @14
    chash
    cfv
    c2
    wceq
    wa
    vp
    wex
    vf
    wex
    #
    vb
    @12
    wral
    #
    va
    cV
    wral
    @3
    cG
    cV
    va
    vm
    vb
    2pthfrgr.v
    @3
    eqid
    #
    2pthfrgrrn2
    @0
    @13
    @16
    va
    cV
    @0
    @1
    cV
    wcel
    #
    wa
    #
    @10
    @15
    vb
    @12
    @19
    @4
    @12
    wcel
    #
    wa
    #
    @9
    @15
    vm
    cV
    @21
    @2
    cV
    wcel
    #
    wa
    #
    @9
    @15
    @23
    @9
    wa
    cG
    cuhgr
    wcel
    #
    @18
    @22
    @4
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @6
    @1
    @4
    wne
    #
    @7
    @5
    @15
    @23
    @27
    @9
    @23
    @24
    @26
    @21
    @24
    @22
    @19
    @24
    @20
    @0
    @24
    @18
    @0
    cG
    cusgr
    wcel
    @24
    cG
    frgrusgr
    cG
    usgruhgr
    syl
    adantr
    adantr
    adantr
    @23
    @18
    @22
    @25
    @0
    @18
    @20
    @22
    simpllr
    @21
    @22
    simpr
    @20
    @25
    @19
    @22
    @4
    cV
    @11
    eldifi
    ad2antlr
    3jca
    jca
    adantr
    @23
    @5
    @6
    @7
    simprrl
    @20
    @28
    @19
    @22
    @9
    @20
    @25
    @4
    @1
    wne
    #
    @28
    @4
    cV
    @1
    eldifsn
    @29
    @28
    @4
    @1
    necom
    biimpi
    simplbiim
    ad3antlr
    @23
    @5
    @6
    @7
    simprrr
    @23
    @5
    @8
    simprl
    @1
    @2
    @4
    vf
    @3
    cG
    cV
    vp
    2pthfrgr.v
    @17
    2pthon3v
    syl131anc
    ex
    rexlimdva
    ralimdva
    ralimdva
    mpd
end
