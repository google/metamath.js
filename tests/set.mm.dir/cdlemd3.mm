include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "simp33.mm"
include "wi.mm"
include "simp1l.mm"
include "simp31.mm"
include "simp32.mm"
include "simp21l.mm"
include "simp233.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "simp22l.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "simp232.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattr.mm"
include "mpan2d.mm"
include "syld.mm"
include "mtod.mm"

theorem cdlemd3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemd3.l: |- .<_ = ( le ` K )
  assume cdlemd3.j: |- .\/ = ( join ` K )
  assume cdlemd3.a: |- A = ( Atoms ` K )
  assume cdlemd3.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ R =/= P ) ) /\ ( R e. A /\ S e. A /\ -. S .<_ ( P .\/ Q ) ) ) -> -. R .<_ ( P .\/ S ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    cQ
    wne
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
    cR
    cP
    wne
    #
    w3a
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
    cS
    @10
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    cR
    cP
    cS
    c.or
    co
    c.le
    wbr
    #
    @17
    @2
    @14
    @15
    @16
    @18
    simp33
    @20
    @21
    cS
    cP
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @20
    @0
    @15
    @16
    @3
    @12
    @21
    @23
    wi
    @0
    @1
    @14
    @19
    simp1l
    #
    @2
    @14
    @15
    @16
    @18
    simp31
    #
    @2
    @14
    @15
    @16
    @18
    simp32
    #
    @3
    @4
    @8
    @13
    @2
    @19
    simp21l
    #
    @9
    @11
    @12
    @5
    @8
    @2
    @19
    simp233
    cA
    cR
    cS
    cP
    c.or
    cK
    c.le
    cdlemd3.l
    cdlemd3.j
    cdlemd3.a
    hlatexch1
    syl131anc
    @20
    @23
    @22
    @10
    c.le
    wbr
    #
    @17
    @20
    cP
    @10
    c.le
    wbr
    #
    @11
    @28
    @20
    @0
    @3
    @6
    @29
    @24
    @27
    @6
    @7
    @5
    @13
    @2
    @19
    simp22l
    #
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemd3.l
    cdlemd3.j
    cdlemd3.a
    hlatlej1
    syl3anc
    @9
    @11
    @12
    @5
    @8
    @2
    @19
    simp232
    @20
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @32
    wcel
    #
    @10
    @32
    wcel
    #
    @29
    @11
    wa
    @28
    wb
    @20
    @0
    @31
    @24
    cK
    hllat
    syl
    #
    @20
    @3
    @33
    @27
    cA
    @32
    cP
    cK
    @32
    eqid
    #
    cdlemd3.a
    atbase
    syl
    #
    @20
    @15
    @34
    @25
    cA
    @32
    cR
    cK
    @37
    cdlemd3.a
    atbase
    syl
    #
    @20
    @31
    @33
    cQ
    @32
    wcel
    #
    @35
    @36
    @38
    @20
    @6
    @40
    @30
    cA
    @32
    cQ
    cK
    @37
    cdlemd3.a
    atbase
    syl
    @32
    c.or
    cK
    cP
    cQ
    @37
    cdlemd3.j
    latjcl
    syl3anc
    #
    @32
    c.or
    cK
    c.le
    cP
    cR
    @10
    @37
    cdlemd3.l
    cdlemd3.j
    latjle12
    syl13anc
    mpbi2and
    @20
    @31
    cS
    @32
    wcel
    #
    @22
    @32
    wcel
    #
    @35
    @23
    @28
    wa
    @17
    wi
    @36
    @20
    @16
    @42
    @26
    cA
    @32
    cS
    cK
    @37
    cdlemd3.a
    atbase
    syl
    @20
    @31
    @33
    @34
    @43
    @36
    @38
    @39
    @32
    c.or
    cK
    cP
    cR
    @37
    cdlemd3.j
    latjcl
    syl3anc
    @41
    @32
    cK
    c.le
    cS
    @22
    @10
    @37
    cdlemd3.l
    lattr
    syl13anc
    mpan2d
    syld
    mtod
end
