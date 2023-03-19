include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "simpll.mm"
include "simplr3.mm"
include "simplr2.mm"
include "simplr1.mm"
include "3jca.mm"
include "jca.mm"
include "simpr.mm"
include "mod1ile.mm"
include "sylc.mm"
include "wceq.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "latmcl.mm"
include "latjcom.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "latjcl.mm"
include "3brtr4d.mm"
include "ex.mm"

theorem mod2ile
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( Z .<_ X -> ( ( X ./\ Y ) .\/ Z ) .<_ ( X ./\ ( Y .\/ Z ) ) ) )

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
    cZ
    cX
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    #
    cZ
    c.or
    co
    #
    cX
    cY
    cZ
    c.or
    co
    #
    c.an
    co
    #
    c.le
    wbr
    @5
    @6
    wa
    #
    cZ
    cY
    cX
    c.an
    co
    #
    c.or
    co
    #
    cZ
    cY
    c.or
    co
    #
    cX
    c.an
    co
    #
    @8
    @10
    c.le
    @11
    @0
    @3
    @2
    @1
    w3a
    #
    wa
    @6
    @13
    @15
    c.le
    wbr
    @11
    @0
    @16
    @0
    @4
    @6
    simpll
    #
    @11
    @3
    @2
    @1
    @1
    @2
    @3
    @0
    @6
    simplr3
    #
    @1
    @2
    @3
    @0
    @6
    simplr2
    #
    @1
    @2
    @3
    @0
    @6
    simplr1
    #
    3jca
    jca
    @5
    @6
    simpr
    cB
    c.or
    cK
    c.le
    c.an
    cZ
    cY
    cX
    modle.b
    modle.l
    modle.j
    modle.m
    mod1ile
    sylc
    @11
    @8
    @12
    cZ
    c.or
    co
    #
    @13
    @11
    @7
    @12
    cZ
    c.or
    @11
    @0
    @1
    @2
    @7
    @12
    wceq
    @17
    @20
    @19
    cB
    cK
    c.an
    cX
    cY
    modle.b
    modle.m
    latmcom
    syl3anc
    oveq1d
    @11
    @0
    @12
    cB
    wcel
    #
    @3
    @21
    @13
    wceq
    @17
    @11
    @0
    @2
    @1
    @22
    @17
    @19
    @20
    cB
    cK
    c.an
    cY
    cX
    modle.b
    modle.m
    latmcl
    syl3anc
    @18
    cB
    c.or
    cK
    @12
    cZ
    modle.b
    modle.j
    latjcom
    syl3anc
    eqtrd
    @11
    @10
    cX
    @14
    c.an
    co
    #
    @15
    @11
    @9
    @14
    cX
    c.an
    @11
    @0
    @2
    @3
    @9
    @14
    wceq
    @17
    @19
    @18
    cB
    c.or
    cK
    cY
    cZ
    modle.b
    modle.j
    latjcom
    syl3anc
    oveq2d
    @11
    @0
    @1
    @14
    cB
    wcel
    #
    @23
    @15
    wceq
    @17
    @20
    @11
    @0
    @3
    @2
    @24
    @17
    @18
    @19
    cB
    c.or
    cK
    cZ
    cY
    modle.b
    modle.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cX
    @14
    modle.b
    modle.m
    latmcom
    syl3anc
    eqtrd
    3brtr4d
    ex
end
