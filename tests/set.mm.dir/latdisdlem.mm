include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "wi.mm"
include "latmcl.mm"
include "3adant3r3.mm"
include "simpr1.mm"
include "simpr3.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "imp.mm"
include "simpl.mm"
include "latjcom.mm"
include "latabs1.mm"
include "eqtrd.mm"
include "adantr.mm"
include "simpr2.mm"
include "latjcl.mm"
include "latmass.mm"
include "syl13anc.mm"
include "latabs2.mm"
include "eqtr3d.mm"
include "3eqtrrd.mm"
include "an32s.mm"
include "ralrimivvva.mm"
include "ex.mm"

theorem latdisdlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  assume latdisd.b: |- B = ( Base ` K )
  assume latdisd.j: |- .\/ = ( join ` K )
  assume latdisd.m: |- ./\ = ( meet ` K )

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ w
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ u
  disjoint ./\ v
  disjoint ./\ w
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  assert |- ( K e. Lat -> ( A. u e. B A. v e. B A. w e. B ( u .\/ ( v ./\ w ) ) = ( ( u .\/ v ) ./\ ( u .\/ w ) ) -> A. x e. B A. y e. B A. z e. B ( x ./\ ( y .\/ z ) ) = ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) )

  proof
    cK
    clat
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    vw
    cv
    #
    c.an
    co
    #
    c.or
    co
    #
    @1
    @2
    c.or
    co
    #
    @1
    @3
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vw
    cB
    wral
    vv
    cB
    wral
    vu
    cB
    wral
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    c.or
    co
    #
    c.an
    co
    #
    @11
    @12
    c.an
    co
    #
    @11
    @13
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
    vy
    cB
    wral
    vx
    cB
    wral
    @0
    @10
    wa
    @19
    vx
    vy
    vz
    cB
    cB
    cB
    @0
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    w3a
    #
    @10
    @19
    @0
    @23
    wa
    #
    @10
    wa
    #
    @18
    @16
    @11
    c.or
    co
    #
    @16
    @13
    c.or
    co
    #
    c.an
    co
    #
    @11
    @13
    @16
    c.or
    co
    #
    c.an
    co
    #
    @15
    @24
    @10
    @18
    @28
    wceq
    #
    @24
    @16
    cB
    wcel
    #
    @20
    @22
    @10
    @31
    wi
    @0
    @20
    @21
    @32
    @22
    cB
    cK
    c.an
    @11
    @12
    latdisd.b
    latdisd.m
    latmcl
    3adant3r3
    #
    @0
    @20
    @21
    @22
    simpr1
    #
    @0
    @20
    @21
    @22
    simpr3
    #
    @9
    @31
    @16
    @4
    c.or
    co
    #
    @16
    @2
    c.or
    co
    #
    @16
    @3
    c.or
    co
    #
    c.an
    co
    #
    wceq
    @16
    @11
    @3
    c.an
    co
    #
    c.or
    co
    #
    @26
    @38
    c.an
    co
    #
    wceq
    vu
    vv
    vw
    @16
    @11
    @13
    cB
    cB
    cB
    @1
    @16
    wceq
    #
    @5
    @36
    @8
    @39
    @1
    @16
    @4
    c.or
    oveq1
    @43
    @6
    @37
    @7
    @38
    c.an
    @1
    @16
    @2
    c.or
    oveq1
    @1
    @16
    @3
    c.or
    oveq1
    oveq12d
    eqeq12d
    vv
    vx
    weq
    #
    @36
    @41
    @39
    @42
    @44
    @4
    @40
    @16
    c.or
    @2
    @11
    @3
    c.an
    oveq1
    #
    oveq2d
    @44
    @37
    @26
    @38
    c.an
    @2
    @11
    @16
    c.or
    oveq2
    oveq1d
    eqeq12d
    vw
    vz
    weq
    #
    @41
    @18
    @42
    @28
    @46
    @40
    @17
    @16
    c.or
    @3
    @13
    @11
    c.an
    oveq2
    oveq2d
    @46
    @38
    @27
    @26
    c.an
    @3
    @13
    @16
    c.or
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    syl3anc
    imp
    @24
    @28
    @30
    wceq
    @10
    @24
    @26
    @11
    @27
    @29
    c.an
    @24
    @26
    @11
    @16
    c.or
    co
    #
    @11
    @24
    @0
    @32
    @20
    @26
    @47
    wceq
    @0
    @23
    simpl
    #
    @33
    @34
    cB
    c.or
    cK
    @16
    @11
    latdisd.b
    latdisd.j
    latjcom
    syl3anc
    @0
    @20
    @21
    @47
    @11
    wceq
    @22
    cB
    c.or
    cK
    c.an
    @11
    @12
    latdisd.b
    latdisd.j
    latdisd.m
    latabs1
    3adant3r3
    eqtrd
    @24
    @0
    @32
    @22
    @27
    @29
    wceq
    @48
    @33
    @35
    cB
    c.or
    cK
    @16
    @13
    latdisd.b
    latdisd.j
    latjcom
    syl3anc
    oveq12d
    adantr
    @25
    @30
    @11
    @13
    @11
    c.or
    co
    #
    @13
    @12
    c.or
    co
    #
    c.an
    co
    #
    c.an
    co
    #
    @15
    @25
    @29
    @51
    @11
    c.an
    @24
    @10
    @29
    @51
    wceq
    #
    @24
    @22
    @20
    @21
    @10
    @53
    wi
    @35
    @34
    @0
    @20
    @21
    @22
    simpr2
    #
    @9
    @53
    @13
    @4
    c.or
    co
    #
    @13
    @2
    c.or
    co
    #
    @13
    @3
    c.or
    co
    #
    c.an
    co
    #
    wceq
    @13
    @40
    c.or
    co
    #
    @49
    @57
    c.an
    co
    #
    wceq
    vu
    vv
    vw
    @13
    @11
    @12
    cB
    cB
    cB
    vu
    vz
    weq
    #
    @5
    @55
    @8
    @58
    @1
    @13
    @4
    c.or
    oveq1
    @61
    @6
    @56
    @7
    @57
    c.an
    @1
    @13
    @2
    c.or
    oveq1
    @1
    @13
    @3
    c.or
    oveq1
    oveq12d
    eqeq12d
    @44
    @55
    @59
    @58
    @60
    @44
    @4
    @40
    @13
    c.or
    @45
    oveq2d
    @44
    @56
    @49
    @57
    c.an
    @2
    @11
    @13
    c.or
    oveq2
    oveq1d
    eqeq12d
    vw
    vy
    weq
    #
    @59
    @29
    @60
    @51
    @62
    @40
    @16
    @13
    c.or
    @3
    @12
    @11
    c.an
    oveq2
    oveq2d
    @62
    @57
    @50
    @49
    c.an
    @3
    @12
    @13
    c.or
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    syl3anc
    imp
    oveq2d
    @24
    @52
    @15
    wceq
    @10
    @24
    @11
    @49
    c.an
    co
    #
    @50
    c.an
    co
    #
    @52
    @15
    @24
    @0
    @20
    @49
    cB
    wcel
    #
    @50
    cB
    wcel
    #
    @64
    @52
    wceq
    @48
    @34
    @24
    @0
    @22
    @20
    @65
    @48
    @35
    @34
    cB
    c.or
    cK
    @13
    @11
    latdisd.b
    latdisd.j
    latjcl
    syl3anc
    @24
    @0
    @22
    @21
    @66
    @48
    @35
    @54
    cB
    c.or
    cK
    @13
    @12
    latdisd.b
    latdisd.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @11
    @49
    @50
    latdisd.b
    latdisd.m
    latmass
    syl13anc
    @24
    @63
    @11
    @50
    @14
    c.an
    @24
    @63
    @11
    @11
    @13
    c.or
    co
    #
    c.an
    co
    #
    @11
    @24
    @49
    @67
    @11
    c.an
    @24
    @0
    @22
    @20
    @49
    @67
    wceq
    @48
    @35
    @34
    cB
    c.or
    cK
    @13
    @11
    latdisd.b
    latdisd.j
    latjcom
    syl3anc
    oveq2d
    @24
    @0
    @20
    @22
    @68
    @11
    wceq
    @48
    @34
    @35
    cB
    c.or
    cK
    c.an
    @11
    @13
    latdisd.b
    latdisd.j
    latdisd.m
    latabs2
    syl3anc
    eqtrd
    @24
    @0
    @22
    @21
    @50
    @14
    wceq
    @48
    @35
    @54
    cB
    c.or
    cK
    @13
    @12
    latdisd.b
    latdisd.j
    latjcom
    syl3anc
    oveq12d
    eqtr3d
    adantr
    eqtrd
    3eqtrrd
    an32s
    ralrimivvva
    ex
end
