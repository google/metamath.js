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
include "w3a.mm"
include "wrex.mm"
include "wral.mm"
include "wne.mm"
include "3cyclfrgrrn.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgredgne.mm"
include "expcom.mm"
include "3ad2ant2.mm"
include "syl5com.mm"
include "adantr.mm"
include "ancrd.mm"
include "reximdv.mm"
include "ralimdv.mm"
include "mpd.mm"

theorem 3cyclfrgrrn2
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let cC: class C
  assume 3cyclfrgrrn1.v: |- V = ( Vtx ` G )
  assume 3cyclfrgrrn1.e: |- E = ( Edg ` G )

  disjoint b c
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint G a
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint G b
  disjoint G c
  disjoint a b
  disjoint a c
  disjoint A a
  disjoint A x
  disjoint A z
  disjoint a x
  disjoint a z
  disjoint x z
  disjoint A b
  disjoint A c
  disjoint A y
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint u y
  disjoint v y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint E x
  disjoint E z
  disjoint E y
  disjoint E u
  disjoint E v
  disjoint G x
  disjoint G z
  disjoint G u
  disjoint G v
  disjoint G y
  disjoint V x
  disjoint V z
  disjoint V y
  disjoint V u
  disjoint V v
  disjoint v x
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` V ) ) -> A. a e. V E. b e. V E. c e. V ( b =/= c /\ ( { a , b } e. E /\ { b , c } e. E /\ { c , a } e. E ) ) )

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
    @4
    vc
    cv
    #
    cpr
    cE
    wcel
    #
    @6
    @3
    cpr
    cE
    wcel
    #
    w3a
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    #
    va
    cV
    wral
    @4
    @6
    wne
    #
    @9
    wa
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    #
    va
    cV
    wral
    cE
    cG
    cV
    va
    vb
    vc
    3cyclfrgrrn1.v
    3cyclfrgrrn1.e
    3cyclfrgrrn
    @2
    @11
    @15
    va
    cV
    @2
    @10
    @14
    vb
    cV
    @2
    @9
    @13
    vc
    cV
    @2
    @9
    @12
    @0
    @9
    @12
    wi
    @1
    @0
    cG
    cusgr
    wcel
    #
    @9
    @12
    cG
    frgrusgr
    @7
    @5
    @16
    @12
    wi
    @8
    @16
    @7
    @12
    cE
    cG
    @4
    @6
    3cyclfrgrrn1.e
    usgredgne
    expcom
    3ad2ant2
    syl5com
    adantr
    ancrd
    reximdv
    reximdv
    ralimdv
    mpd
end
