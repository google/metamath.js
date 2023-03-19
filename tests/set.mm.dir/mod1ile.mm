include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simpr.mm"
include "wb.mm"
include "latjcl.mm"
include "simplr3.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latmlej12.mm"
include "latmle2.mm"
include "latmcl.mm"
include "latjle12.mm"
include "ex.mm"

theorem mod1ile
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume modle.b: |- B = ( Base ` K )
  assume modle.l: |- .<_ = ( le ` K )
  assume modle.j: |- .\/ = ( join ` K )
  assume modle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ Z -> ( X .\/ ( Y ./\ Z ) ) .<_ ( ( X .\/ Y ) ./\ Z ) ) )

  proof
    cK
    clat
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
    cZ
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cZ
    c.le
    wbr
    #
    cX
    cY
    cZ
    c.an
    co
    #
    c.or
    co
    cX
    cY
    c.or
    co
    #
    cZ
    c.an
    co
    #
    c.le
    wbr
    #
    @5
    @6
    wa
    #
    cX
    @9
    c.le
    wbr
    #
    @7
    @9
    c.le
    wbr
    #
    @10
    @11
    cX
    @8
    c.le
    wbr
    #
    @6
    @12
    @11
    @0
    @1
    @2
    @14
    @0
    @4
    @6
    simpll
    #
    @1
    @2
    @3
    @0
    @6
    simplr1
    #
    @1
    @2
    @3
    @0
    @6
    simplr2
    #
    cB
    c.or
    cK
    c.le
    cX
    cY
    modle.b
    modle.l
    modle.j
    latlej1
    syl3anc
    @5
    @6
    simpr
    @11
    @0
    @1
    @8
    cB
    wcel
    #
    @3
    @14
    @6
    wa
    @12
    wb
    @15
    @16
    @11
    @0
    @1
    @2
    @18
    @15
    @16
    @17
    cB
    c.or
    cK
    cX
    cY
    modle.b
    modle.j
    latjcl
    syl3anc
    #
    @1
    @2
    @3
    @0
    @6
    simplr3
    #
    cB
    cK
    c.le
    c.an
    cX
    @8
    cZ
    modle.b
    modle.l
    modle.m
    latlem12
    syl13anc
    mpbi2and
    @11
    @7
    @8
    c.le
    wbr
    #
    @7
    cZ
    c.le
    wbr
    #
    @13
    @11
    @0
    @2
    @3
    @1
    @21
    @15
    @17
    @20
    @16
    cB
    c.or
    cK
    c.le
    c.an
    cY
    cZ
    cX
    modle.b
    modle.l
    modle.j
    modle.m
    latmlej12
    syl13anc
    @11
    @0
    @2
    @3
    @22
    @15
    @17
    @20
    cB
    cK
    c.le
    c.an
    cY
    cZ
    modle.b
    modle.l
    modle.m
    latmle2
    syl3anc
    @11
    @0
    @7
    cB
    wcel
    #
    @18
    @3
    @21
    @22
    wa
    @13
    wb
    @15
    @11
    @0
    @2
    @3
    @23
    @15
    @17
    @20
    cB
    cK
    c.an
    cY
    cZ
    modle.b
    modle.m
    latmcl
    syl3anc
    #
    @19
    @20
    cB
    cK
    c.le
    c.an
    @7
    @8
    cZ
    modle.b
    modle.l
    modle.m
    latlem12
    syl13anc
    mpbi2and
    @11
    @0
    @1
    @23
    @9
    cB
    wcel
    #
    @12
    @13
    wa
    @10
    wb
    @15
    @16
    @24
    @11
    @0
    @18
    @3
    @25
    @15
    @19
    @20
    cB
    cK
    c.an
    @8
    cZ
    modle.b
    modle.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cX
    @7
    @9
    modle.b
    modle.l
    modle.j
    latjle12
    syl13anc
    mpbi2and
    ex
end
