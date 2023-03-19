include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "simp1l.mm"
include "simp1r1.mm"
include "simp2.mm"
include "simp1r3.mm"
include "simp3.mm"
include "3atlem3.mm"
include "syl131anc.mm"
include "3expia.mm"
include "simp11.mm"
include "simp123.mm"
include "simp122.mm"
include "simp121.mm"
include "3jca.mm"
include "simp131.mm"
include "simp132.mm"
include "jca.mm"
include "simp21.mm"
include "simp22.mm"
include "hlatexch2.mm"
include "mtod.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latnlej1r.mm"
include "3atlem4.mm"
include "syl321anc.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "latj31.mm"
include "syl13anc.mm"
include "breq1d.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "pm2.61ne.mm"
include "3impia.mm"

theorem 3atlem5
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3at.l: |- .<_ = ( le ` K )
  assume 3at.j: |- .\/ = ( join ` K )
  assume 3at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= Q /\ -. Q .<_ ( P .\/ U ) ) /\ ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ U ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ U ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cP
    cQ
    wne
    #
    cQ
    cP
    cU
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    @10
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @16
    @18
    wceq
    #
    @9
    @15
    wa
    #
    @19
    @20
    wi
    @16
    @17
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @16
    @22
    wceq
    #
    wi
    cP
    cU
    cP
    cU
    wceq
    #
    @19
    @23
    @20
    @24
    @25
    @18
    @22
    @16
    c.le
    @18
    @22
    wceq
    cU
    cP
    cU
    cP
    @17
    c.or
    oveq2
    eqcoms
    #
    breq2d
    @25
    @18
    @22
    @16
    @26
    eqeq2d
    imbi12d
    @21
    cP
    cU
    wne
    #
    @19
    @20
    @21
    @27
    @19
    w3a
    @9
    @12
    @27
    @14
    @19
    @20
    @9
    @15
    @27
    @19
    simp1l
    @12
    @13
    @14
    @9
    @27
    @19
    simp1r1
    @21
    @27
    @19
    simp2
    @12
    @13
    @14
    @9
    @27
    @19
    simp1r3
    @21
    @27
    @19
    simp3
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem3
    syl131anc
    3expia
    @21
    cR
    cQ
    c.or
    co
    #
    cP
    c.or
    co
    #
    @22
    c.le
    wbr
    #
    @29
    @22
    wceq
    #
    @23
    @24
    @9
    @15
    @30
    @31
    @9
    @15
    @30
    w3a
    #
    @0
    @3
    @2
    @1
    w3a
    @5
    @6
    wa
    cP
    @28
    c.le
    wbr
    #
    wn
    cR
    cQ
    wne
    #
    @30
    @31
    @0
    @4
    @8
    @15
    @30
    simp11
    #
    @32
    @3
    @2
    @1
    @1
    @2
    @3
    @0
    @8
    @15
    @30
    simp123
    #
    @1
    @2
    @3
    @0
    @8
    @15
    @30
    simp122
    #
    @1
    @2
    @3
    @0
    @8
    @15
    @30
    simp121
    #
    3jca
    @32
    @5
    @6
    @5
    @6
    @7
    @0
    @4
    @15
    @30
    simp131
    @5
    @6
    @7
    @0
    @4
    @15
    @30
    simp132
    jca
    @32
    @33
    @11
    @9
    @12
    @13
    @14
    @30
    simp21
    #
    @32
    @0
    @1
    @3
    @2
    @13
    @33
    @11
    wi
    @35
    @38
    @36
    @37
    @9
    @12
    @13
    @14
    @30
    simp22
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    hlatexch2
    syl131anc
    mtod
    @32
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @41
    wcel
    #
    cQ
    @41
    wcel
    #
    @12
    @34
    @32
    @0
    @40
    @35
    cK
    hllat
    #
    syl
    @32
    @3
    @42
    @36
    cA
    @41
    cR
    cK
    @41
    eqid
    #
    3at.a
    atbase
    #
    syl
    @32
    @1
    @43
    @38
    cA
    @41
    cP
    cK
    @46
    3at.a
    atbase
    #
    syl
    @32
    @2
    @44
    @37
    cA
    @41
    cQ
    cK
    @46
    3at.a
    atbase
    #
    syl
    @39
    @41
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @46
    3at.l
    3at.j
    latnlej1r
    syl131anc
    @9
    @15
    @30
    simp3
    cA
    cR
    cQ
    cP
    cS
    cT
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem4
    syl321anc
    3expia
    @21
    @16
    @29
    @22
    c.le
    @21
    @40
    @43
    @44
    @42
    @16
    @29
    wceq
    @21
    @0
    @40
    @0
    @4
    @8
    @15
    simpl1
    @45
    syl
    @21
    @1
    @43
    @1
    @2
    @3
    @0
    @8
    @15
    simpl21
    @48
    syl
    @21
    @2
    @44
    @1
    @2
    @3
    @0
    @8
    @15
    simpl22
    @49
    syl
    @21
    @3
    @42
    @1
    @2
    @3
    @0
    @8
    @15
    simpl23
    @47
    syl
    @41
    c.or
    cK
    cP
    cQ
    cR
    @46
    3at.j
    latj31
    syl13anc
    #
    breq1d
    @21
    @16
    @29
    @22
    @50
    eqeq1d
    3imtr4d
    pm2.61ne
    3impia
end
