include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cmee.mm"
include "cfv.mm"
include "wsbc.mm"
include "cjn.mm"
include "cbs.mm"
include "clat.mm"
include "cdlat.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wb.mm"
include "wa.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "simpr.mm"
include "eqidd.mm"
include "simpl.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "sylan9bb.mm"
include "3impb.mm"
include "sbc3ie.mm"
include "syl6bb.mm"
include "df-dlat.mm"
include "elrab2.mm"

theorem isdlat
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let vb: setvar b
  let vk: setvar k
  let vj: setvar j
  let vm: setvar m
  assume isdlat.b: |- B = ( Base ` K )
  assume isdlat.j: |- .\/ = ( join ` K )
  assume isdlat.m: |- ./\ = ( meet ` K )

  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint b k
  disjoint j k
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint K k
  disjoint b j
  disjoint b m
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint K b
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint K j
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint K m
  disjoint B k
  disjoint B b
  disjoint B j
  disjoint B m
  disjoint .\/ k
  disjoint .\/ b
  disjoint .\/ j
  disjoint .\/ m
  disjoint ./\ k
  disjoint ./\ b
  disjoint ./\ j
  disjoint ./\ m
  assert |- ( K e. DLat <-> ( K e. Lat /\ A. x e. B A. y e. B A. z e. B ( x ./\ ( y .\/ z ) ) = ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    vj
    cv
    #
    co
    #
    vm
    cv
    #
    co
    #
    @0
    @1
    @5
    co
    #
    @0
    @2
    @5
    co
    #
    @3
    co
    #
    wceq
    #
    vz
    vb
    cv
    #
    wral
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    vm
    vk
    cv
    #
    cmee
    cfv
    #
    wsbc
    #
    vj
    @15
    cjn
    cfv
    #
    wsbc
    #
    vb
    @15
    cbs
    cfv
    #
    wsbc
    #
    @0
    @1
    @2
    c.or
    co
    #
    c.an
    co
    #
    @0
    @1
    c.an
    co
    #
    @0
    @2
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vk
    cK
    clat
    cdlat
    @15
    cK
    wceq
    #
    @21
    @14
    vm
    c.an
    wsbc
    #
    vj
    c.or
    wsbc
    #
    vb
    cB
    wsbc
    @29
    @30
    @19
    @32
    vb
    @20
    cB
    @30
    @20
    cK
    cbs
    cfv
    #
    cB
    @15
    cK
    cbs
    fveq2
    isdlat.b
    syl6eqr
    @30
    @17
    @31
    vj
    @18
    c.or
    @30
    @18
    cK
    cjn
    cfv
    #
    c.or
    @15
    cK
    cjn
    fveq2
    isdlat.j
    syl6eqr
    @30
    @14
    vm
    @16
    c.an
    @30
    @16
    cK
    cmee
    cfv
    #
    c.an
    @15
    cK
    cmee
    fveq2
    isdlat.m
    syl6eqr
    sbceq1d
    sbceqbid
    sbceqbid
    @14
    @29
    vb
    vj
    vm
    cB
    c.or
    c.an
    cB
    @33
    cvv
    isdlat.b
    cK
    cbs
    fvex
    eqeltri
    c.or
    @34
    cvv
    isdlat.j
    cK
    cjn
    fvex
    eqeltri
    c.an
    @35
    cvv
    isdlat.m
    cK
    cmee
    fvex
    eqeltri
    @11
    cB
    wceq
    #
    @3
    c.or
    wceq
    #
    @5
    c.an
    wceq
    #
    @14
    @29
    wb
    @36
    @14
    @10
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @37
    @38
    wa
    #
    @29
    @13
    @40
    vx
    @11
    cB
    @12
    @39
    vy
    @11
    cB
    @10
    vz
    @11
    cB
    raleq
    raleqbi1dv
    raleqbi1dv
    @41
    @39
    @28
    vx
    vy
    cB
    cB
    @41
    @10
    @27
    vz
    cB
    @41
    @6
    @23
    @9
    @26
    @41
    @0
    @0
    @4
    @22
    @5
    c.an
    @37
    @38
    simpr
    #
    @41
    @0
    eqidd
    @41
    @3
    c.or
    @1
    @2
    @37
    @38
    simpl
    #
    oveqd
    oveq123d
    @41
    @7
    @24
    @8
    @25
    @3
    c.or
    @43
    @41
    @5
    c.an
    @0
    @1
    @42
    oveqd
    @41
    @5
    c.an
    @0
    @2
    @42
    oveqd
    oveq123d
    eqeq12d
    ralbidv
    2ralbidv
    sylan9bb
    3impb
    sbc3ie
    syl6bb
    vx
    vy
    vz
    vj
    vk
    vm
    vb
    df-dlat
    elrab2
end
