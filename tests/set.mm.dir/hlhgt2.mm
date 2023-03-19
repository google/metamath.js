include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "hlhgt4.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "ad3antrrr.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "syl.mm"
include "simpllr.mm"
include "simplr.mm"
include "plttr.mm"
include "syl13anc.mm"
include "simpr.mm"
include "op1cl.mm"
include "anim12d.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem hlhgt2
  let vx: setvar x
  let cB: class B
  let c.lt: class .<
  let c.1: class .1.
  let cK: class K
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume hlhgt4.b: |- B = ( Base ` K )
  assume hlhgt4.s: |- .< = ( lt ` K )
  assume hlhgt4.z: |- .0. = ( 0. ` K )
  assume hlhgt4.u: |- .1. = ( 1. ` K )

  disjoint B x
  disjoint K x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K y
  disjoint K z
  disjoint .< y
  disjoint .< z
  disjoint .1. y
  disjoint .1. z
  disjoint .0. y
  disjoint .0. z
  assert |- ( K e. HL -> E. x e. B ( .0. .< x /\ x .< .1. ) )

  proof
    cK
    chlt
    wcel
    #
    c.0
    vy
    cv
    #
    c.lt
    wbr
    @1
    vx
    cv
    #
    c.lt
    wbr
    wa
    #
    @2
    vz
    cv
    #
    c.lt
    wbr
    @4
    c.1
    c.lt
    wbr
    wa
    #
    wa
    #
    vz
    cB
    wrex
    #
    vx
    cB
    wrex
    #
    vy
    cB
    wrex
    c.0
    @2
    c.lt
    wbr
    #
    @2
    c.1
    c.lt
    wbr
    #
    wa
    #
    vx
    cB
    wrex
    #
    vy
    vx
    vz
    cB
    c.lt
    c.1
    cK
    c.0
    hlhgt4.b
    hlhgt4.s
    hlhgt4.z
    hlhgt4.u
    hlhgt4
    @0
    @8
    @12
    vy
    cB
    @0
    @1
    cB
    wcel
    #
    wa
    #
    @7
    @11
    vx
    cB
    @14
    @2
    cB
    wcel
    #
    wa
    #
    @6
    @11
    vz
    cB
    @16
    @4
    cB
    wcel
    #
    wa
    #
    @3
    @9
    @5
    @10
    @18
    cK
    cpo
    wcel
    #
    c.0
    cB
    wcel
    #
    @13
    @15
    @3
    @9
    wi
    @0
    @19
    @13
    @15
    @17
    cK
    hlpos
    ad3antrrr
    #
    @18
    cK
    cops
    wcel
    #
    @20
    @0
    @22
    @13
    @15
    @17
    cK
    hlop
    ad3antrrr
    #
    cB
    cK
    c.0
    hlhgt4.b
    hlhgt4.z
    op0cl
    syl
    @0
    @13
    @15
    @17
    simpllr
    @14
    @15
    @17
    simplr
    #
    cB
    c.lt
    cK
    c.0
    @1
    @2
    hlhgt4.b
    hlhgt4.s
    plttr
    syl13anc
    @18
    @19
    @15
    @17
    c.1
    cB
    wcel
    #
    @5
    @10
    wi
    @21
    @24
    @16
    @17
    simpr
    @18
    @22
    @25
    @23
    cB
    c.1
    cK
    hlhgt4.b
    hlhgt4.u
    op1cl
    syl
    cB
    c.lt
    cK
    @2
    @4
    c.1
    hlhgt4.b
    hlhgt4.s
    plttr
    syl13anc
    anim12d
    rexlimdva
    reximdva
    rexlimdva
    mpd
end
