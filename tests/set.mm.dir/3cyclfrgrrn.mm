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
include "wi.mm"
include "wne.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashgt12el2.mm"
include "mp3an1.mm"
include "simpr.mm"
include "pm3.22.mm"
include "3adant2.mm"
include "adantr.mm"
include "simpl2.mm"
include "3cyclfrgrrn1.mm"
include "syl3anc.mm"
include "3exp1.mm"
include "rexlimiv.mm"
include "syl.mm"
include "expcom.mm"
include "pm2.43a.mm"
include "com13.mm"
include "imp.mm"
include "ralrimiv.mm"

theorem 3cyclfrgrrn
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
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` V ) ) -> A. a e. V E. b e. V E. c e. V ( { a , b } e. E /\ { b , c } e. E /\ { c , a } e. E ) )

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
    va
    cv
    #
    vb
    cv
    #
    cpr
    cE
    wcel
    @3
    vc
    cv
    #
    cpr
    cE
    wcel
    @4
    @2
    cpr
    cE
    wcel
    w3a
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    va
    cV
    @0
    @1
    @2
    cV
    wcel
    #
    @5
    wi
    @6
    @1
    @0
    @5
    @1
    @6
    @0
    @5
    wi
    #
    @1
    @6
    @6
    @7
    wi
    #
    @1
    @6
    wa
    @2
    vx
    cv
    #
    wne
    #
    vx
    cV
    wrex
    #
    @8
    cV
    cvv
    wcel
    @1
    @6
    @11
    cV
    cG
    cvtx
    cfv
    cvv
    3cyclfrgrrn1.v
    cG
    cvtx
    fvex
    eqeltri
    @2
    cV
    cvv
    vx
    hashgt12el2
    mp3an1
    @10
    @8
    vx
    cV
    @9
    cV
    wcel
    #
    @10
    @6
    @0
    @5
    @12
    @10
    @6
    w3a
    #
    @0
    wa
    @0
    @6
    @12
    wa
    #
    @10
    @5
    @13
    @0
    simpr
    @13
    @14
    @0
    @12
    @6
    @14
    @10
    @12
    @6
    pm3.22
    3adant2
    adantr
    @12
    @10
    @6
    @0
    simpl2
    @2
    @9
    cE
    cG
    cV
    vb
    vc
    3cyclfrgrrn1.v
    3cyclfrgrrn1.e
    3cyclfrgrrn1
    syl3anc
    3exp1
    rexlimiv
    syl
    expcom
    pm2.43a
    com13
    imp
    ralrimiv
end
