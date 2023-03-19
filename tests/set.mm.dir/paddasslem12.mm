include "chlt.mm"
include "wcel.mm"
include "weq.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "simpl1l.mm"
include "simpl21.mm"
include "simpl22.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "simpl23.mm"
include "3jca.mm"
include "sspadd2.mm"
include "paddss1.mm"
include "sylc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simprll.mm"
include "simprlr.mm"
include "simpl3l.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "atbase.mm"
include "sseldd.mm"
include "simpl3r.mm"
include "latjcl.mm"
include "simpl1r.mm"
include "simprrl.mm"
include "oveq1.mm"
include "breq2d.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "latlej1.mm"
include "simprrr.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "elpaddri.mm"
include "syl322anc.mm"

theorem paddasslem12
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
  let vr: setvar r
  let vp: setvar p
  let vs: setvar s
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( ( K e. HL /\ x = y ) /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ r e. A ) ) /\ ( ( y e. Y /\ z e. Z ) /\ ( p .<_ ( x .\/ r ) /\ r .<_ ( y .\/ z ) ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    vx
    vy
    weq
    #
    wa
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
    vr
    cv
    #
    cA
    wcel
    #
    wa
    #
    w3a
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
    wa
    #
    @7
    vx
    cv
    #
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    @13
    @15
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    cY
    cZ
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    @7
    @25
    @0
    @27
    cA
    wss
    #
    @5
    w3a
    cY
    @27
    wss
    #
    @26
    @28
    wss
    @25
    @0
    @29
    @5
    @0
    @1
    @6
    @11
    @24
    simpl1l
    #
    @25
    @0
    @3
    @4
    @29
    @31
    @3
    @4
    @5
    @2
    @11
    @24
    simpl21
    #
    @3
    @4
    @5
    @2
    @11
    @24
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
    @3
    @4
    @5
    @2
    @11
    @24
    simpl23
    #
    3jca
    @25
    @0
    @4
    @3
    @30
    @31
    @33
    @32
    cA
    chlt
    c.pl
    cK
    cY
    cX
    paddasslem.a
    paddasslem.p
    sspadd2
    syl3anc
    cA
    chlt
    c.pl
    cK
    cY
    @27
    cZ
    paddasslem.a
    paddasslem.p
    paddss1
    sylc
    @25
    cK
    clat
    wcel
    #
    @4
    @5
    @14
    @16
    @8
    @7
    @21
    c.le
    wbr
    @7
    @26
    wcel
    @25
    @0
    @35
    @31
    cK
    hllat
    syl
    #
    @33
    @34
    @12
    @14
    @16
    @23
    simprll
    #
    @12
    @14
    @16
    @23
    simprlr
    #
    @8
    @10
    @2
    @6
    @24
    simpl3l
    #
    @25
    cK
    cbs
    cfv
    #
    cK
    c.le
    @7
    @13
    @9
    c.or
    co
    #
    @21
    @40
    eqid
    #
    paddasslem.l
    @36
    @25
    @8
    @7
    @40
    wcel
    @39
    cA
    @40
    @7
    cK
    @42
    paddasslem.a
    atbase
    syl
    @25
    @35
    @13
    @40
    wcel
    #
    @9
    @40
    wcel
    #
    @41
    @40
    wcel
    @36
    @25
    @13
    cA
    wcel
    @43
    @25
    cY
    cA
    @13
    @33
    @37
    sseldd
    cA
    @40
    @13
    cK
    @42
    paddasslem.a
    atbase
    syl
    #
    @25
    @10
    @44
    @8
    @10
    @2
    @6
    @24
    simpl3r
    cA
    @40
    @9
    cK
    @42
    paddasslem.a
    atbase
    syl
    #
    @40
    c.or
    cK
    @13
    @9
    @42
    paddasslem.j
    latjcl
    syl3anc
    @25
    @35
    @43
    @15
    @40
    wcel
    #
    @21
    @40
    wcel
    #
    @36
    @45
    @25
    @15
    cA
    wcel
    @47
    @25
    cZ
    cA
    @15
    @34
    @38
    sseldd
    cA
    @40
    @15
    cK
    @42
    paddasslem.a
    atbase
    syl
    #
    @40
    c.or
    cK
    @13
    @15
    @42
    paddasslem.j
    latjcl
    syl3anc
    #
    @25
    @1
    @20
    @7
    @41
    c.le
    wbr
    #
    @0
    @1
    @6
    @11
    @24
    simpl1r
    @12
    @17
    @20
    @22
    simprrl
    @1
    @20
    @51
    @1
    @19
    @41
    @7
    c.le
    @18
    @13
    @9
    c.or
    oveq1
    breq2d
    biimpa
    syl2anc
    @25
    @13
    @21
    c.le
    wbr
    #
    @22
    @41
    @21
    c.le
    wbr
    #
    @25
    @35
    @43
    @47
    @52
    @36
    @45
    @49
    @40
    c.or
    cK
    c.le
    @13
    @15
    @42
    paddasslem.l
    paddasslem.j
    latlej1
    syl3anc
    @12
    @17
    @20
    @22
    simprrr
    @25
    @35
    @43
    @44
    @48
    @52
    @22
    wa
    @53
    wb
    @36
    @45
    @46
    @50
    @40
    c.or
    cK
    c.le
    @13
    @9
    @21
    @42
    paddasslem.l
    paddasslem.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
    cA
    c.pl
    @13
    @15
    @7
    c.or
    cK
    c.le
    cY
    cZ
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    elpaddri
    syl322anc
    sseldd
end
