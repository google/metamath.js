include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "clpl.mm"
include "cfv.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl11.mm"
include "hllat.mm"
include "syl.mm"
include "simpl12.mm"
include "eqid.mm"
include "atbase.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "latj4.mm"
include "syl122anc.mm"
include "simpr.mm"
include "syl5eqelr.mm"
include "clln.mm"
include "wb.mm"
include "simpl31.mm"
include "llni2.mm"
include "syl31anc.mm"
include "simpl32.mm"
include "2llnmj.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "simpl23.mm"
include "simpl33.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem arglem1N
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  assume arglem1.j: |- .\/ = ( join ` K )
  assume arglem1.m: |- ./\ = ( meet ` K )
  assume arglem1.a: |- A = ( Atoms ` K )
  assume arglem1.f: |- F = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume arglem1.g: |- G = ( ( P .\/ S ) ./\ ( Q .\/ T ) )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( S e. A /\ T e. A /\ P =/= Q ) /\ ( P =/= S /\ Q =/= T /\ S =/= T ) ) /\ G e. A ) -> F e. A )

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
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cS
    wne
    #
    cQ
    cT
    wne
    #
    cS
    cT
    wne
    #
    w3a
    #
    w3a
    #
    cG
    cA
    wcel
    #
    wa
    #
    cF
    cP
    cQ
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    c.an
    co
    #
    cA
    arglem1.f
    @14
    @17
    cA
    wcel
    #
    @15
    @16
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
    @19
    cP
    cS
    c.or
    co
    #
    cQ
    cT
    c.or
    co
    #
    c.or
    co
    #
    @20
    @14
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
    cQ
    @26
    wcel
    #
    cS
    @26
    wcel
    #
    cT
    @26
    wcel
    #
    @19
    @24
    wceq
    @14
    @0
    @25
    @0
    @1
    @2
    @7
    @11
    @13
    simpl11
    #
    cK
    hllat
    syl
    @14
    @1
    @27
    @0
    @1
    @2
    @7
    @11
    @13
    simpl12
    #
    cA
    @26
    cP
    cK
    @26
    eqid
    #
    arglem1.a
    atbase
    syl
    @14
    @2
    @28
    @0
    @1
    @2
    @7
    @11
    @13
    simpl13
    #
    cA
    @26
    cQ
    cK
    @33
    arglem1.a
    atbase
    syl
    @14
    @4
    @29
    @4
    @5
    @6
    @3
    @11
    @13
    simpl21
    #
    cA
    @26
    cS
    cK
    @33
    arglem1.a
    atbase
    syl
    @14
    @5
    @30
    @4
    @5
    @6
    @3
    @11
    @13
    simpl22
    #
    cA
    @26
    cT
    cK
    @33
    arglem1.a
    atbase
    syl
    @26
    c.or
    cK
    cT
    cP
    cQ
    cS
    @33
    arglem1.j
    latj4
    syl122anc
    @14
    @22
    @23
    c.an
    co
    #
    cA
    wcel
    #
    @24
    @20
    wcel
    #
    @14
    @37
    cG
    cA
    arglem1.g
    @12
    @13
    simpr
    syl5eqelr
    @14
    @0
    @22
    cK
    clln
    cfv
    #
    wcel
    #
    @23
    @40
    wcel
    #
    @38
    @39
    wb
    @31
    @14
    @0
    @1
    @4
    @8
    @41
    @31
    @32
    @35
    @8
    @9
    @10
    @3
    @7
    @13
    simpl31
    cA
    cP
    cS
    c.or
    cK
    @40
    arglem1.j
    arglem1.a
    @40
    eqid
    #
    llni2
    syl31anc
    @14
    @0
    @2
    @5
    @9
    @42
    @31
    @34
    @36
    @8
    @9
    @10
    @3
    @7
    @13
    simpl32
    cA
    cQ
    cT
    c.or
    cK
    @40
    arglem1.j
    arglem1.a
    @43
    llni2
    syl31anc
    cA
    @20
    c.or
    cK
    c.an
    @40
    @22
    @23
    arglem1.j
    arglem1.m
    arglem1.a
    @43
    @20
    eqid
    #
    2llnmj
    syl3anc
    mpbid
    eqeltrd
    @14
    @0
    @15
    @40
    wcel
    #
    @16
    @40
    wcel
    #
    @18
    @21
    wb
    @31
    @14
    @0
    @1
    @2
    @6
    @45
    @31
    @32
    @34
    @4
    @5
    @6
    @3
    @11
    @13
    simpl23
    cA
    cP
    cQ
    c.or
    cK
    @40
    arglem1.j
    arglem1.a
    @43
    llni2
    syl31anc
    @14
    @0
    @4
    @5
    @10
    @46
    @31
    @35
    @36
    @8
    @9
    @10
    @3
    @7
    @13
    simpl33
    cA
    cS
    cT
    c.or
    cK
    @40
    arglem1.j
    arglem1.a
    @43
    llni2
    syl31anc
    cA
    @20
    c.or
    cK
    c.an
    @40
    @15
    @16
    arglem1.j
    arglem1.m
    arglem1.a
    @43
    @44
    2llnmj
    syl3anc
    mpbird
    syl5eqel
end
