include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "simpl1l.mm"
include "simpl21.mm"
include "simpl22.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "simpl23.mm"
include "sspadd1.mm"
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
include "simprrr.mm"
include "latlej1.mm"
include "simprrl.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "elpaddri.mm"
include "syl322anc.mm"

theorem paddasslem13
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


  assert |- ( ( ( ( K e. HL /\ p =/= z ) /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ r e. A ) ) /\ ( ( x e. X /\ y e. Y ) /\ ( r .<_ ( x .\/ y ) /\ p .<_ ( x .\/ r ) ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    vp
    cv
    #
    vz
    cv
    wne
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
    @1
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
    wa
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
    @1
    @13
    @9
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
    cX
    cY
    c.pl
    co
    #
    @25
    cZ
    c.pl
    co
    #
    @1
    @24
    @0
    @25
    cA
    wss
    #
    @6
    @25
    @26
    wss
    @0
    @2
    @7
    @11
    @23
    simpl1l
    #
    @24
    @0
    @4
    @5
    @27
    @28
    @4
    @5
    @6
    @3
    @11
    @23
    simpl21
    #
    @4
    @5
    @6
    @3
    @11
    @23
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
    @4
    @5
    @6
    @3
    @11
    @23
    simpl23
    cA
    chlt
    c.pl
    cK
    @25
    cZ
    paddasslem.a
    paddasslem.p
    sspadd1
    syl3anc
    @24
    cK
    clat
    wcel
    #
    @4
    @5
    @14
    @16
    @8
    @1
    @18
    c.le
    wbr
    @1
    @25
    wcel
    @24
    @0
    @31
    @28
    cK
    hllat
    syl
    #
    @29
    @30
    @12
    @14
    @16
    @22
    simprll
    #
    @12
    @14
    @16
    @22
    simprlr
    #
    @8
    @10
    @3
    @7
    @23
    simpl3l
    #
    @24
    cK
    cbs
    cfv
    #
    cK
    c.le
    @1
    @20
    @18
    @36
    eqid
    #
    paddasslem.l
    @32
    @24
    @8
    @1
    @36
    wcel
    @35
    cA
    @36
    @1
    cK
    @37
    paddasslem.a
    atbase
    syl
    @24
    @31
    @13
    @36
    wcel
    #
    @9
    @36
    wcel
    #
    @20
    @36
    wcel
    @32
    @24
    @13
    cA
    wcel
    @38
    @24
    cX
    cA
    @13
    @29
    @33
    sseldd
    cA
    @36
    @13
    cK
    @37
    paddasslem.a
    atbase
    syl
    #
    @24
    @10
    @39
    @8
    @10
    @3
    @7
    @23
    simpl3r
    cA
    @36
    @9
    cK
    @37
    paddasslem.a
    atbase
    syl
    #
    @36
    c.or
    cK
    @13
    @9
    @37
    paddasslem.j
    latjcl
    syl3anc
    @24
    @31
    @38
    @15
    @36
    wcel
    #
    @18
    @36
    wcel
    #
    @32
    @40
    @24
    @15
    cA
    wcel
    @42
    @24
    cY
    cA
    @15
    @30
    @34
    sseldd
    cA
    @36
    @15
    cK
    @37
    paddasslem.a
    atbase
    syl
    #
    @36
    c.or
    cK
    @13
    @15
    @37
    paddasslem.j
    latjcl
    syl3anc
    #
    @12
    @17
    @19
    @21
    simprrr
    @24
    @13
    @18
    c.le
    wbr
    #
    @19
    @20
    @18
    c.le
    wbr
    #
    @24
    @31
    @38
    @42
    @46
    @32
    @40
    @44
    @36
    c.or
    cK
    c.le
    @13
    @15
    @37
    paddasslem.l
    paddasslem.j
    latlej1
    syl3anc
    @12
    @17
    @19
    @21
    simprrl
    @24
    @31
    @38
    @39
    @43
    @46
    @19
    wa
    @47
    wb
    @32
    @40
    @41
    @45
    @36
    c.or
    cK
    c.le
    @13
    @9
    @18
    @37
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
    @1
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
    sseldd
end
