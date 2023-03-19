include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "latmle1.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "wb.mm"
include "latmcl.mm"
include "simpr1.mm"
include "3jca.mm"
include "latjle12.mm"
include "syldan.mm"
include "mpbi2and.mm"
include "latmle2.mm"
include "wi.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "latjlej12.mm"
include "syl122anc.mm"
include "mp2and.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "3adant3r1.mm"
include "latlem12.mm"
include "syl13anc.mm"

theorem latledi
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latledi.b: |- B = ( Base ` K )
  assume latledi.l: |- .<_ = ( le ` K )
  assume latledi.j: |- .\/ = ( join ` K )
  assume latledi.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) .\/ ( X ./\ Z ) ) .<_ ( X ./\ ( Y .\/ Z ) ) )

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
    cY
    c.an
    co
    #
    cX
    cZ
    c.an
    co
    #
    c.or
    co
    #
    cX
    c.le
    wbr
    #
    @8
    cY
    cZ
    c.or
    co
    #
    c.le
    wbr
    #
    @8
    cX
    @10
    c.an
    co
    c.le
    wbr
    #
    @5
    @6
    cX
    c.le
    wbr
    #
    @7
    cX
    c.le
    wbr
    #
    @9
    @0
    @1
    @2
    @13
    @3
    cB
    cK
    c.le
    c.an
    cX
    cY
    latledi.b
    latledi.l
    latledi.m
    latmle1
    3adant3r3
    @0
    @1
    @3
    @14
    @2
    cB
    cK
    c.le
    c.an
    cX
    cZ
    latledi.b
    latledi.l
    latledi.m
    latmle1
    3adant3r2
    @0
    @4
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @1
    w3a
    @13
    @14
    wa
    @9
    wb
    @5
    @15
    @16
    @1
    @0
    @1
    @2
    @15
    @3
    cB
    cK
    c.an
    cX
    cY
    latledi.b
    latledi.m
    latmcl
    3adant3r3
    #
    @0
    @1
    @3
    @16
    @2
    cB
    cK
    c.an
    cX
    cZ
    latledi.b
    latledi.m
    latmcl
    3adant3r2
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    3jca
    cB
    c.or
    cK
    c.le
    @6
    @7
    cX
    latledi.b
    latledi.l
    latledi.j
    latjle12
    syldan
    mpbi2and
    @5
    @6
    cY
    c.le
    wbr
    #
    @7
    cZ
    c.le
    wbr
    #
    @11
    @0
    @1
    @2
    @20
    @3
    cB
    cK
    c.le
    c.an
    cX
    cY
    latledi.b
    latledi.l
    latledi.m
    latmle2
    3adant3r3
    @0
    @1
    @3
    @21
    @2
    cB
    cK
    c.le
    c.an
    cX
    cZ
    latledi.b
    latledi.l
    latledi.m
    latmle2
    3adant3r2
    @5
    @0
    @15
    @2
    @16
    @3
    @20
    @21
    wa
    @11
    wi
    @0
    @4
    simpl
    #
    @17
    @0
    @1
    @2
    @3
    simpr2
    @18
    @0
    @1
    @2
    @3
    simpr3
    cB
    c.or
    cK
    c.le
    cZ
    @6
    cY
    @7
    latledi.b
    latledi.l
    latledi.j
    latjlej12
    syl122anc
    mp2and
    @5
    @0
    @8
    cB
    wcel
    #
    @1
    @10
    cB
    wcel
    #
    @9
    @11
    wa
    @12
    wb
    @22
    @5
    @0
    @15
    @16
    @23
    @22
    @17
    @18
    cB
    c.or
    cK
    @6
    @7
    latledi.b
    latledi.j
    latjcl
    syl3anc
    @19
    @0
    @2
    @3
    @24
    @1
    cB
    c.or
    cK
    cY
    cZ
    latledi.b
    latledi.j
    latjcl
    3adant3r1
    cB
    cK
    c.le
    c.an
    @8
    cX
    @10
    latledi.b
    latledi.l
    latledi.m
    latlem12
    syl13anc
    mpbi2and
end
