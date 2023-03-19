include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wa.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wne.mm"
include "2pthfrgrrn.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgredgne.mm"
include "ex.mm"
include "anim12d.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ancld.mm"
include "reximdva.mm"
include "ralimdvva.mm"
include "mpd.mm"

theorem 2pthfrgrrn2
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume 2pthfrgrrn.v: |- V = ( Vtx ` G )
  assume 2pthfrgrrn.e: |- E = ( Edg ` G )

  disjoint G a
  disjoint G b
  disjoint G c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint V a
  disjoint V b
  disjoint V c
  assert |- ( G e. FriendGraph -> A. a e. V A. c e. ( V \ { a } ) E. b e. V ( ( { a , b } e. E /\ { b , c } e. E ) /\ ( a =/= b /\ b =/= c ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    cE
    wcel
    #
    @2
    vc
    cv
    #
    cpr
    cE
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    vc
    cV
    @1
    csn
    cdif
    #
    wral
    va
    cV
    wral
    @6
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
    vb
    cV
    wrex
    #
    vc
    @8
    wral
    va
    cV
    wral
    cE
    cG
    cV
    va
    vb
    vc
    2pthfrgrrn.v
    2pthfrgrrn.e
    2pthfrgrrn
    @0
    @7
    @13
    va
    vc
    cV
    @8
    @0
    @1
    cV
    wcel
    @4
    @8
    wcel
    wa
    #
    wa
    #
    @6
    @12
    vb
    cV
    @15
    @2
    cV
    wcel
    #
    wa
    @6
    @11
    @0
    @6
    @11
    wi
    #
    @14
    @16
    @0
    cG
    cusgr
    wcel
    #
    @17
    cG
    frgrusgr
    @18
    @3
    @9
    @5
    @10
    @18
    @3
    @9
    cE
    cG
    @1
    @2
    2pthfrgrrn.e
    usgredgne
    ex
    @18
    @5
    @10
    cE
    cG
    @2
    @4
    2pthfrgrrn.e
    usgredgne
    ex
    anim12d
    syl
    ad2antrr
    ancld
    reximdva
    ralimdvva
    mpd
end
