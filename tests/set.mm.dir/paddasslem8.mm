include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "clat.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "simpl21.mm"
include "simpl22.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "simpl23.mm"
include "simpr11.mm"
include "simpr12.mm"
include "simpl3r.mm"
include "simpr2.mm"
include "elpaddri.mm"
include "syl322anc.mm"
include "simpr13.mm"
include "simpl3l.mm"
include "simpr3.mm"

theorem paddasslem8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vp: setvar p
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ s e. A ) ) /\ ( ( x e. X /\ y e. Y /\ z e. Z ) /\ s .<_ ( x .\/ y ) /\ p .<_ ( s .\/ z ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    #
    vs
    cv
    #
    cA
    wcel
    #
    wa
    #
    w3a
    #
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cY
    wcel
    #
    vz
    cv
    #
    cZ
    wcel
    #
    w3a
    #
    @7
    @11
    @13
    c.or
    co
    c.le
    wbr
    #
    @5
    @7
    @15
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    cK
    clat
    wcel
    #
    cX
    cY
    c.pl
    co
    #
    cA
    wss
    #
    @3
    @7
    @23
    wcel
    #
    @16
    @6
    @19
    @5
    @23
    cZ
    c.pl
    co
    wcel
    @21
    @0
    @22
    @0
    @4
    @9
    @20
    simpl1
    #
    cK
    hllat
    syl
    #
    @21
    @0
    @1
    @2
    @24
    @26
    @1
    @2
    @3
    @0
    @9
    @20
    simpl21
    #
    @1
    @2
    @3
    @0
    @9
    @20
    simpl22
    #
    cA
    chlt
    c.pl
    cK
    cX
    cY
    paddasslem.a
    paddasslem.p
    paddssat
    syl3anc
    @1
    @2
    @3
    @0
    @9
    @20
    simpl23
    @21
    @22
    @1
    @2
    @12
    @14
    @8
    @18
    @25
    @27
    @28
    @29
    @12
    @14
    @16
    @18
    @19
    @10
    simpr11
    @12
    @14
    @16
    @18
    @19
    @10
    simpr12
    @6
    @8
    @0
    @4
    @20
    simpl3r
    @10
    @17
    @18
    @19
    simpr2
    cA
    c.pl
    @11
    @13
    @7
    c.or
    cK
    c.le
    cX
    cY
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    elpaddri
    syl322anc
    @12
    @14
    @16
    @18
    @19
    @10
    simpr13
    @6
    @8
    @0
    @4
    @20
    simpl3l
    @10
    @17
    @18
    @19
    simpr3
    cA
    c.pl
    @7
    @15
    @5
    c.or
    cK
    c.le
    @23
    cZ
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    elpaddri
    syl322anc
end
