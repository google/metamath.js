include "cupgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "upgredg.mm"
include "3adant3.mm"
include "wa.mm"
include "wi.mm"
include "elpr2elpr.mm"
include "3expia.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "com13.mm"
include "3ad2ant3.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem upgredg2vtx
  let cA: class A
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vx: setvar x
  let va: setvar a
  let vc: setvar c
  assume upgredg.v: |- V = ( Vtx ` G )
  assume upgredg.e: |- E = ( Edg ` G )

  disjoint C b
  disjoint G b
  disjoint V b
  disjoint A b
  disjoint C x
  disjoint G x
  disjoint V x
  disjoint C a
  disjoint C c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint G a
  disjoint V a
  disjoint V c
  disjoint A a
  disjoint A c
  disjoint E a
  disjoint E c
  disjoint G c
  assert |- ( ( G e. UPGraph /\ C e. E /\ A e. C ) -> E. b e. V C = { A , b } )

  proof
    cG
    cupgr
    wcel
    #
    cC
    cE
    wcel
    #
    cA
    cC
    wcel
    #
    w3a
    #
    cC
    va
    cv
    #
    vc
    cv
    #
    cpr
    #
    wceq
    #
    vc
    cV
    wrex
    va
    cV
    wrex
    #
    cC
    cA
    vb
    cv
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    #
    @0
    @1
    @8
    @2
    cC
    cE
    cG
    cV
    va
    vc
    upgredg.v
    upgredg.e
    upgredg
    3adant3
    @3
    @7
    @11
    va
    vc
    cV
    cV
    @2
    @0
    @4
    cV
    wcel
    #
    @5
    cV
    wcel
    #
    wa
    #
    @7
    @11
    wi
    wi
    @1
    @7
    @14
    @2
    @11
    @14
    @2
    @11
    wi
    @7
    cA
    @6
    wcel
    #
    @6
    @9
    wceq
    #
    vb
    cV
    wrex
    #
    wi
    @12
    @13
    @15
    @17
    cA
    cV
    @4
    @5
    vb
    elpr2elpr
    3expia
    @7
    @2
    @15
    @11
    @17
    cC
    @6
    cA
    eleq2
    @7
    @10
    @16
    vb
    cV
    cC
    @6
    @9
    eqeq1
    rexbidv
    imbi12d
    syl5ibr
    com13
    3ad2ant3
    rexlimdvv
    mpd
end
