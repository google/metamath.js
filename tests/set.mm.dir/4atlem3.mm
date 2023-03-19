include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "clvol.mm"
include "cfv.mm"
include "simpl11.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr.mm"
include "eqid.mm"
include "lvoli2.mm"
include "syl121anc.mm"
include "simpl23.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "lvolnle3at.mm"
include "syl23anc.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "atbase.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simpl12.mm"
include "simpl13.mm"
include "anbi12d.mm"
include "wceq.mm"
include "latjass.mm"
include "breq1d.mm"
include "3bitr4d.mm"
include "mtbird.mm"
include "ianor.mm"
include "orbi12i.mm"
include "bitri.mm"
include "sylib.mm"

theorem 4atlem3
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
  let cV: class V
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( U e. A /\ V e. A ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( -. P .<_ ( ( T .\/ U ) .\/ V ) \/ -. Q .<_ ( ( T .\/ U ) .\/ V ) ) \/ ( -. R .<_ ( ( T .\/ U ) .\/ V ) \/ -. S .<_ ( ( T .\/ U ) .\/ V ) ) ) )

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
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
    #
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cS
    @12
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    wa
    #
    cP
    cT
    cU
    c.or
    co
    #
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    cQ
    @17
    c.le
    wbr
    #
    wa
    #
    cR
    @17
    c.le
    wbr
    #
    cS
    @17
    c.le
    wbr
    #
    wa
    #
    wa
    #
    wn
    #
    @18
    wn
    @19
    wn
    wo
    #
    @21
    wn
    @22
    wn
    wo
    #
    wo
    #
    @15
    @24
    @13
    cS
    c.or
    co
    #
    @17
    c.le
    wbr
    #
    @15
    @0
    @29
    cK
    clvol
    cfv
    #
    wcel
    #
    @6
    @8
    @9
    @30
    wn
    @0
    @1
    @2
    @7
    @10
    @14
    simpl11
    #
    @15
    @3
    @4
    @5
    @14
    @32
    @3
    @7
    @10
    @14
    simpl1
    #
    @4
    @5
    @6
    @3
    @10
    @14
    simpl21
    #
    @4
    @5
    @6
    @3
    @10
    @14
    simpl22
    #
    @11
    @14
    simpr
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    @31
    4at.l
    4at.j
    4at.a
    @31
    eqid
    #
    lvoli2
    syl121anc
    @4
    @5
    @6
    @3
    @10
    @14
    simpl23
    #
    @8
    @9
    @3
    @7
    @14
    simpl3l
    #
    @8
    @9
    @3
    @7
    @14
    simpl3r
    #
    cA
    cT
    cU
    cV
    c.or
    cK
    c.le
    @31
    @29
    4at.l
    4at.j
    4at.a
    @37
    lvolnle3at
    syl23anc
    @15
    @12
    @17
    c.le
    wbr
    #
    cR
    cS
    c.or
    co
    #
    @17
    c.le
    wbr
    #
    wa
    #
    @12
    @42
    c.or
    co
    #
    @17
    c.le
    wbr
    #
    @24
    @30
    @15
    cK
    clat
    wcel
    #
    @12
    cK
    cbs
    cfv
    #
    wcel
    #
    @42
    @48
    wcel
    #
    @17
    @48
    wcel
    #
    @44
    @46
    wb
    @15
    @0
    @47
    @33
    cK
    hllat
    syl
    #
    @15
    @3
    @49
    @34
    cA
    @48
    c.or
    cK
    cP
    cQ
    @48
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl
    #
    @15
    @0
    @4
    @5
    @50
    @33
    @35
    @36
    cA
    @48
    c.or
    cK
    cR
    cS
    @53
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @15
    @47
    @16
    @48
    wcel
    #
    cV
    @48
    wcel
    #
    @51
    @52
    @15
    @0
    @6
    @8
    @55
    @33
    @38
    @39
    cA
    @48
    c.or
    cK
    cT
    cU
    @53
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @15
    @9
    @56
    @40
    cA
    @48
    cV
    cK
    @53
    4at.a
    atbase
    syl
    @48
    c.or
    cK
    @16
    cV
    @53
    4at.j
    latjcl
    syl3anc
    #
    @48
    c.or
    cK
    c.le
    @12
    @42
    @17
    @53
    4at.l
    4at.j
    latjle12
    syl13anc
    @15
    @20
    @41
    @23
    @43
    @15
    @47
    cP
    @48
    wcel
    #
    cQ
    @48
    wcel
    #
    @51
    @20
    @41
    wb
    @52
    @15
    @1
    @58
    @0
    @1
    @2
    @7
    @10
    @14
    simpl12
    cA
    @48
    cP
    cK
    @53
    4at.a
    atbase
    syl
    @15
    @2
    @59
    @0
    @1
    @2
    @7
    @10
    @14
    simpl13
    cA
    @48
    cQ
    cK
    @53
    4at.a
    atbase
    syl
    @57
    @48
    c.or
    cK
    c.le
    cP
    cQ
    @17
    @53
    4at.l
    4at.j
    latjle12
    syl13anc
    @15
    @47
    cR
    @48
    wcel
    #
    cS
    @48
    wcel
    #
    @51
    @23
    @43
    wb
    @52
    @15
    @4
    @60
    @35
    cA
    @48
    cR
    cK
    @53
    4at.a
    atbase
    syl
    #
    @15
    @5
    @61
    @36
    cA
    @48
    cS
    cK
    @53
    4at.a
    atbase
    syl
    #
    @57
    @48
    c.or
    cK
    c.le
    cR
    cS
    @17
    @53
    4at.l
    4at.j
    latjle12
    syl13anc
    anbi12d
    @15
    @29
    @45
    @17
    c.le
    @15
    @47
    @49
    @60
    @61
    @29
    @45
    wceq
    @52
    @54
    @62
    @63
    @48
    c.or
    cK
    @12
    cR
    cS
    @53
    4at.j
    latjass
    syl13anc
    breq1d
    3bitr4d
    mtbird
    @25
    @20
    wn
    #
    @23
    wn
    #
    wo
    @28
    @20
    @23
    ianor
    @64
    @26
    @65
    @27
    @18
    @19
    ianor
    @21
    @22
    ianor
    orbi12i
    bitri
    sylib
end
