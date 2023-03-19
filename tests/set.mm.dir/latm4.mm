include "col.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "latm12.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "clat.mm"
include "ollat.mm"
include "3ad2ant1.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmassOLD.mm"
include "3eqtr4d.mm"

theorem latm4
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X ./\ Y ) ./\ ( Z ./\ W ) ) = ( ( X ./\ Z ) ./\ ( Y ./\ W ) ) )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    cZ
    cW
    c.an
    co
    #
    c.an
    co
    #
    c.an
    co
    #
    cX
    cZ
    cY
    cW
    c.an
    co
    #
    c.an
    co
    #
    c.an
    co
    #
    cX
    cY
    c.an
    co
    @8
    c.an
    co
    #
    cX
    cZ
    c.an
    co
    @11
    c.an
    co
    #
    @7
    @9
    @12
    cX
    c.an
    @7
    @0
    @2
    @4
    @5
    @9
    @12
    wceq
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    cB
    cK
    c.an
    cY
    cZ
    cW
    olmass.b
    olmass.m
    latm12
    syl13anc
    oveq2d
    @7
    @0
    @1
    @2
    @8
    cB
    wcel
    #
    @14
    @10
    wceq
    @16
    @0
    @1
    @2
    @6
    simp2l
    #
    @17
    @7
    cK
    clat
    wcel
    #
    @4
    @5
    @20
    @0
    @3
    @22
    @6
    cK
    ollat
    3ad2ant1
    #
    @18
    @19
    cB
    cK
    c.an
    cZ
    cW
    olmass.b
    olmass.m
    latmcl
    syl3anc
    cB
    cK
    c.an
    cX
    cY
    @8
    olmass.b
    olmass.m
    latmassOLD
    syl13anc
    @7
    @0
    @1
    @4
    @11
    cB
    wcel
    #
    @15
    @13
    wceq
    @16
    @21
    @18
    @7
    @22
    @2
    @5
    @24
    @23
    @17
    @19
    cB
    cK
    c.an
    cY
    cW
    olmass.b
    olmass.m
    latmcl
    syl3anc
    cB
    cK
    c.an
    cX
    cZ
    @11
    olmass.b
    olmass.m
    latmassOLD
    syl13anc
    3eqtr4d
end
