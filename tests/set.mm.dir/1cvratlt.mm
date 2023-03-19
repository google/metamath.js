include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simprl.mm"
include "1cvratex.mm"
include "syl3anc.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "simp1l3.mm"
include "simp1rr.mm"
include "simp3.mm"
include "atlelt.mm"
include "syl132anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem 1cvratlt
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.lt: class .<
  let c.1: class .1.
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vq: setvar q
  assume 1cvratlt.b: |- B = ( Base ` K )
  assume 1cvratlt.l: |- .<_ = ( le ` K )
  assume 1cvratlt.s: |- .< = ( lt ` K )
  assume 1cvratlt.u: |- .1. = ( 1. ` K )
  assume 1cvratlt.c: |- C = ( <o ` K )
  assume 1cvratlt.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ X e. B ) /\ ( X C .1. /\ P .<_ X ) ) -> P .< X )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cX
    c.1
    cC
    wbr
    #
    cP
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vq
    cv
    #
    cX
    c.lt
    wbr
    #
    vq
    cA
    wrex
    #
    cP
    cX
    c.lt
    wbr
    #
    @7
    @0
    @2
    @4
    @10
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl3
    @3
    @4
    @5
    simprl
    cA
    cB
    cC
    c.lt
    c.1
    cK
    cX
    vq
    1cvratlt.b
    1cvratlt.s
    1cvratlt.u
    1cvratlt.c
    1cvratlt.a
    1cvratex
    syl3anc
    @7
    @9
    @11
    vq
    cA
    @7
    @8
    cA
    wcel
    #
    @9
    w3a
    @0
    @1
    @12
    @2
    @5
    @9
    @11
    @0
    @1
    @2
    @6
    @12
    @9
    simp1l1
    @0
    @1
    @2
    @6
    @12
    @9
    simp1l2
    @7
    @12
    @9
    simp2
    @0
    @1
    @2
    @6
    @12
    @9
    simp1l3
    @4
    @5
    @3
    @12
    @9
    simp1rr
    @7
    @12
    @9
    simp3
    cA
    cB
    cP
    @8
    c.lt
    cK
    c.le
    cX
    1cvratlt.b
    1cvratlt.l
    1cvratlt.s
    1cvratlt.a
    atlelt
    syl132anc
    rexlimdv3a
    mpd
end
