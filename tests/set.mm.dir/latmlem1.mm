include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "latmle1.mm"
include "3adant3r2.mm"
include "wi.mm"
include "simpl.mm"
include "latmcl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "latmle2.mm"
include "jctird.mm"
include "wb.mm"
include "simpr3.mm"
include "3jca.mm"
include "latlem12.mm"
include "syldan.mm"
include "sylibd.mm"

theorem latmlem1
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ Y -> ( X ./\ Z ) .<_ ( Y ./\ Z ) ) )

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
    c.le
    wbr
    #
    cX
    cZ
    c.an
    co
    #
    cY
    c.le
    wbr
    #
    @7
    cZ
    c.le
    wbr
    #
    wa
    #
    @7
    cY
    cZ
    c.an
    co
    c.le
    wbr
    #
    @5
    @6
    @8
    @9
    @5
    @7
    cX
    c.le
    wbr
    #
    @6
    @8
    @0
    @1
    @3
    @12
    @2
    cB
    cK
    c.le
    c.an
    cX
    cZ
    latmle.b
    latmle.l
    latmle.m
    latmle1
    3adant3r2
    @5
    @0
    @7
    cB
    wcel
    #
    @1
    @2
    @12
    @6
    wa
    @8
    wi
    @0
    @4
    simpl
    @0
    @1
    @3
    @13
    @2
    cB
    cK
    c.an
    cX
    cZ
    latmle.b
    latmle.m
    latmcl
    3adant3r2
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    #
    cB
    cK
    c.le
    @7
    cX
    cY
    latmle.b
    latmle.l
    lattr
    syl13anc
    mpand
    @0
    @1
    @3
    @9
    @2
    cB
    cK
    c.le
    c.an
    cX
    cZ
    latmle.b
    latmle.l
    latmle.m
    latmle2
    3adant3r2
    jctird
    @0
    @4
    @13
    @2
    @3
    w3a
    @10
    @11
    wb
    @5
    @13
    @2
    @3
    @14
    @15
    @0
    @1
    @2
    @3
    simpr3
    3jca
    cB
    cK
    c.le
    c.an
    @7
    cY
    cZ
    latmle.b
    latmle.l
    latmle.m
    latlem12
    syldan
    sylibd
end
