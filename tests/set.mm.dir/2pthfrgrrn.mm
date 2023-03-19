include "cfrgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "frgrusgrfrcond.mm"
include "wi.mm"
include "reurex.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anbi1i.mm"
include "zfpair2.mm"
include "prss.mm"
include "sylbbr.mm"
include "reximi.mm"
include "syl.mm"
include "a1i.mm"
include "ralimdvva.mm"
include "imp.mm"
include "sylbi.mm"

theorem 2pthfrgrrn
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
  assert |- ( G e. FriendGraph -> A. a e. V A. c e. ( V \ { a } ) E. b e. V ( { a , b } e. E /\ { b , c } e. E ) )

  proof
    cG
    cfrgr
    wcel
    cG
    cusgr
    wcel
    #
    vb
    cv
    #
    va
    cv
    #
    cpr
    #
    @1
    vc
    cv
    #
    cpr
    #
    cpr
    cE
    wss
    #
    vb
    cV
    wreu
    #
    vc
    cV
    @2
    csn
    cdif
    #
    wral
    va
    cV
    wral
    #
    wa
    @2
    @1
    cpr
    #
    cE
    wcel
    #
    @5
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
    @8
    wral
    va
    cV
    wral
    #
    vb
    va
    cE
    cG
    cV
    vc
    2pthfrgrrn.v
    2pthfrgrrn.e
    frgrusgrfrcond
    @0
    @9
    @15
    @0
    @7
    @14
    va
    vc
    cV
    @8
    @7
    @14
    wi
    @0
    @2
    cV
    wcel
    @4
    @8
    wcel
    wa
    wa
    @7
    @6
    vb
    cV
    wrex
    @14
    @6
    vb
    cV
    reurex
    @6
    @13
    vb
    cV
    @13
    @3
    cE
    wcel
    #
    @12
    wa
    @6
    @11
    @16
    @12
    @10
    @3
    cE
    @2
    @1
    prcom
    eleq1i
    anbi1i
    @3
    @5
    cE
    vb
    va
    zfpair2
    vb
    vc
    zfpair2
    prss
    sylbbr
    reximi
    syl
    a1i
    ralimdvva
    imp
    sylbi
end
