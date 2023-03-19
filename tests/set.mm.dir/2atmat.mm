include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "clpl.mm"
include "cfv.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "atbase.mm"
include "simp22.mm"
include "latjass.mm"
include "syl13anc.mm"
include "simp33.mm"
include "wb.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latleeqj2.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "simp23.mm"
include "simp32.mm"
include "wa.mm"
include "simp12.mm"
include "simp13.mm"
include "islpln2a.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "clln.mm"
include "llni2.mm"
include "syl31anc.mm"
include "simp31.mm"
include "2llnmj.mm"
include "mpbird.mm"

theorem 2atmat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume 2atmat.l: |- .<_ = ( le ` K )
  assume 2atmat.j: |- .\/ = ( join ` K )
  assume 2atmat.m: |- ./\ = ( meet ` K )
  assume 2atmat.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ P =/= Q ) /\ ( R =/= S /\ -. R .<_ ( P .\/ Q ) /\ S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( P .\/ Q ) ./\ ( R .\/ S ) ) e. A )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cR
    cS
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
    wn
    #
    cS
    @9
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @9
    cR
    cS
    c.or
    co
    #
    c.an
    co
    cA
    wcel
    #
    @9
    @15
    c.or
    co
    #
    cK
    clpl
    cfv
    #
    wcel
    #
    @14
    @17
    @11
    @18
    @14
    @11
    cS
    c.or
    co
    #
    @17
    @11
    @14
    cK
    clat
    wcel
    #
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @22
    wcel
    #
    cS
    @22
    wcel
    #
    @20
    @17
    wceq
    @14
    @0
    @21
    @0
    @1
    @2
    @7
    @13
    simp11
    #
    cK
    hllat
    syl
    #
    @3
    @7
    @23
    @13
    cA
    @22
    c.or
    cK
    cP
    cQ
    @22
    eqid
    #
    2atmat.j
    2atmat.a
    hlatjcl
    3ad2ant1
    #
    @14
    @4
    @24
    @3
    @4
    @5
    @6
    @13
    simp21
    #
    cA
    @22
    cR
    cK
    @28
    2atmat.a
    atbase
    syl
    #
    @14
    @5
    @25
    @3
    @4
    @5
    @6
    @13
    simp22
    #
    cA
    @22
    cS
    cK
    @28
    2atmat.a
    atbase
    syl
    #
    @22
    c.or
    cK
    @9
    cR
    cS
    @28
    2atmat.j
    latjass
    syl13anc
    @14
    @12
    @20
    @11
    wceq
    #
    @3
    @7
    @8
    @10
    @12
    simp33
    @14
    @21
    @25
    @11
    @22
    wcel
    #
    @12
    @34
    wb
    @27
    @33
    @14
    @21
    @23
    @24
    @35
    @27
    @29
    @31
    @22
    c.or
    cK
    @9
    cR
    @28
    2atmat.j
    latjcl
    syl3anc
    @22
    c.or
    cK
    c.le
    cS
    @11
    @28
    2atmat.l
    2atmat.j
    latleeqj2
    syl3anc
    mpbid
    eqtr3d
    @14
    @11
    @18
    wcel
    #
    @6
    @10
    @3
    @4
    @5
    @6
    @13
    simp23
    #
    @3
    @7
    @8
    @10
    @12
    simp32
    @14
    @0
    @1
    @2
    @4
    @36
    @6
    @10
    wa
    wb
    @26
    @0
    @1
    @2
    @7
    @13
    simp12
    #
    @0
    @1
    @2
    @7
    @13
    simp13
    #
    @30
    cA
    @18
    cP
    cQ
    cR
    c.or
    cK
    c.le
    2atmat.l
    2atmat.j
    2atmat.a
    @18
    eqid
    #
    islpln2a
    syl13anc
    mpbir2and
    eqeltrd
    @14
    @0
    @9
    cK
    clln
    cfv
    #
    wcel
    #
    @15
    @41
    wcel
    #
    @16
    @19
    wb
    @26
    @14
    @0
    @1
    @2
    @6
    @42
    @26
    @38
    @39
    @37
    cA
    cP
    cQ
    c.or
    cK
    @41
    2atmat.j
    2atmat.a
    @41
    eqid
    #
    llni2
    syl31anc
    @14
    @0
    @4
    @5
    @8
    @43
    @26
    @30
    @32
    @3
    @7
    @8
    @10
    @12
    simp31
    cA
    cR
    cS
    c.or
    cK
    @41
    2atmat.j
    2atmat.a
    @44
    llni2
    syl31anc
    cA
    @18
    c.or
    cK
    c.an
    @41
    @9
    @15
    2atmat.j
    2atmat.m
    2atmat.a
    @44
    @40
    2llnmj
    syl3anc
    mpbird
end
