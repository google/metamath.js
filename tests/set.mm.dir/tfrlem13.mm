include "crecs.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "word.mm"
include "wn.mm"
include "tfrlem8.mm"
include "ordirr.mm"
include "ax-mp.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wss.mm"
include "eqid.mm"
include "tfrlem12.mm"
include "cuni.mm"
include "elssuni.mm"
include "recsfval.mm"
include "syl6sseqr.mm"
include "dmss.mm"
include "3syl.mm"
include "csuc.mm"
include "con0.mm"
include "a1i.mm"
include "dmexg.mm"
include "elon2.mm"
include "sylanbrc.mm"
include "sucidg.mm"
include "syl.mm"
include "wfn.mm"
include "wceq.mm"
include "tfrlem10.mm"
include "fndm.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "mto.mm"

theorem tfrlem13
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- -. recs ( F ) e. _V

  proof
    cF
    crecs
    #
    cvv
    wcel
    #
    @0
    cdm
    #
    @2
    wcel
    #
    @2
    word
    #
    @3
    wn
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    #
    @2
    ordirr
    ax-mp
    @1
    @0
    @2
    @0
    cF
    cfv
    cop
    csn
    cun
    #
    cdm
    #
    @2
    @2
    @1
    @6
    cA
    wcel
    #
    @6
    @0
    wss
    @7
    @2
    wss
    vx
    vy
    cA
    @6
    vf
    cF
    tfrlem.1
    @6
    eqid
    #
    tfrlem12
    @8
    @6
    cA
    cuni
    @0
    @6
    cA
    elssuni
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    syl6sseqr
    @6
    @0
    dmss
    3syl
    @1
    @2
    @2
    csuc
    #
    @7
    @1
    @2
    con0
    wcel
    #
    @2
    @10
    wcel
    @1
    @4
    @2
    cvv
    wcel
    @11
    @4
    @1
    @5
    a1i
    @0
    cvv
    dmexg
    @2
    elon2
    sylanbrc
    #
    @2
    con0
    sucidg
    syl
    @1
    @11
    @6
    @10
    wfn
    @7
    @10
    wceq
    @12
    vx
    vy
    cA
    @6
    vf
    cF
    tfrlem.1
    @9
    tfrlem10
    @10
    @6
    fndm
    3syl
    eleqtrrd
    sseldd
    mto
end
