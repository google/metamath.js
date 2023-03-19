include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cconn.mm"
include "cpw.mm"
include "crab.mm"
include "ciun.mm"
include "cuni.mm"
include "uniiun.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "simpl.mm"
include "simpr.mm"
include "weq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "simprd.mm"
include "iunconn.mm"
include "syl5eqel.mm"

theorem conncompconn
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T
  assume conncomp.2: |- S = U. { x e. ~P X | ( A e. x /\ ( J |`t x ) e. Conn ) }

  disjoint A x
  disjoint J x
  disjoint X x
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B k
  disjoint B x
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint T y
  disjoint X k
  disjoint X y
  disjoint X z
  assert |- ( ( J e. ( TopOn ` X ) /\ A e. X ) -> ( J |`t S ) e. Conn )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cJ
    cS
    crest
    co
    cJ
    vy
    cA
    vx
    cv
    #
    wcel
    #
    cJ
    @3
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    vx
    cX
    cpw
    #
    crab
    #
    vy
    cv
    #
    ciun
    #
    crest
    co
    cconn
    cS
    @11
    cJ
    crest
    cS
    @9
    cuni
    @11
    conncomp.2
    vy
    @9
    uniiun
    eqtri
    oveq2i
    @2
    @9
    @10
    cA
    vy
    cJ
    cX
    @0
    @1
    simpl
    @2
    @10
    @9
    wcel
    #
    wa
    #
    @10
    cX
    @13
    @10
    @8
    wcel
    #
    cA
    @10
    wcel
    #
    cJ
    @10
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    @13
    @12
    @14
    @18
    wa
    @2
    @12
    simpr
    @7
    @18
    vx
    @10
    @8
    vx
    vy
    weq
    #
    @4
    @15
    @6
    @17
    @3
    @10
    cA
    eleq2
    @19
    @5
    @16
    cconn
    @3
    @10
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    elrab
    sylib
    #
    simpld
    elpwid
    @13
    @15
    @17
    @13
    @14
    @18
    @20
    simprd
    #
    simpld
    @13
    @15
    @17
    @21
    simprd
    iunconn
    syl5eqel
end
