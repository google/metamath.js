include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "oveq1.mm"
include "simpl1.mm"
include "simpl3.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "simprl.mm"
include "simprr.mm"
include "3atnelvolN.mm"
include "syl13anc.mm"
include "adantr.mm"
include "eqneltrd.mm"
include "ex.mm"
include "necon2ad.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "hlatjcl.mm"
include "latleeqj2.mm"
include "syl3anc.mm"
include "simpl2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "con2d.mm"
include "ad2antll.mm"
include "latjcl.mm"
include "eleq1.mm"
include "3jcad.mm"
include "lvoli2.mm"
include "3expia.mm"
include "impbid.mm"

theorem islvol2aN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume islvol2a.l: |- .<_ = ( le ` K )
  assume islvol2a.j: |- .\/ = ( join ` K )
  assume islvol2a.a: |- A = ( Atoms ` K )
  assume islvol2a.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( ( ( P .\/ Q ) .\/ R ) .\/ S ) e. V <-> ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) )

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
    wa
    #
    wa
    #
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    cV
    wcel
    #
    cP
    cQ
    wne
    #
    cR
    @8
    c.le
    wbr
    #
    wn
    #
    cS
    @9
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @7
    @11
    @12
    @14
    @16
    @7
    @11
    cP
    cQ
    @7
    cP
    cQ
    wceq
    #
    @11
    wn
    #
    @7
    @18
    wa
    #
    @10
    cQ
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    cV
    @20
    @9
    @21
    cS
    c.or
    @20
    @8
    cQ
    cR
    c.or
    @18
    @7
    @8
    cQ
    cQ
    c.or
    co
    #
    cQ
    cP
    cQ
    cQ
    c.or
    oveq1
    @7
    @0
    @2
    @23
    cQ
    wceq
    @0
    @1
    @2
    @6
    simpl1
    #
    @0
    @1
    @2
    @6
    simpl3
    #
    cA
    c.or
    cK
    cQ
    islvol2a.j
    islvol2a.a
    hlatjidm
    syl2anc
    sylan9eqr
    oveq1d
    oveq1d
    @7
    @22
    cV
    wcel
    wn
    #
    @18
    @7
    @0
    @2
    @4
    @5
    @26
    @24
    @25
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    #
    cA
    cQ
    cR
    cS
    c.or
    cK
    cV
    islvol2a.j
    islvol2a.a
    islvol2a.v
    3atnelvolN
    syl13anc
    adantr
    eqneltrd
    ex
    necon2ad
    @7
    @13
    @11
    @7
    @13
    @9
    @8
    wceq
    #
    @19
    @7
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
    @8
    @31
    wcel
    #
    @13
    @29
    wb
    @7
    @0
    @30
    @24
    cK
    hllat
    syl
    #
    @4
    @32
    @3
    @5
    cA
    @31
    cR
    cK
    @31
    eqid
    #
    islvol2a.a
    atbase
    ad2antrl
    #
    @3
    @33
    @6
    cA
    @31
    c.or
    cK
    cP
    cQ
    @35
    islvol2a.j
    islvol2a.a
    hlatjcl
    adantr
    #
    @31
    c.or
    cK
    c.le
    cR
    @8
    @35
    islvol2a.l
    islvol2a.j
    latleeqj2
    syl3anc
    @7
    @19
    @29
    @8
    cS
    c.or
    co
    #
    cV
    wcel
    #
    wn
    #
    @7
    @0
    @1
    @2
    @5
    @40
    @24
    @0
    @1
    @2
    @6
    simpl2
    #
    @25
    @28
    cA
    cP
    cQ
    cS
    c.or
    cK
    cV
    islvol2a.j
    islvol2a.a
    islvol2a.v
    3atnelvolN
    syl13anc
    @29
    @11
    @39
    @29
    @10
    @38
    cV
    @9
    @8
    cS
    c.or
    oveq1
    eleq1d
    notbid
    syl5ibrcom
    sylbid
    con2d
    @7
    @15
    @11
    @7
    @15
    @10
    @9
    wceq
    #
    @19
    @7
    @30
    cS
    @31
    wcel
    #
    @9
    @31
    wcel
    #
    @15
    @42
    wb
    @34
    @5
    @43
    @3
    @4
    cA
    @31
    cS
    cK
    @35
    islvol2a.a
    atbase
    ad2antll
    @7
    @30
    @33
    @32
    @44
    @34
    @37
    @36
    @31
    c.or
    cK
    @8
    cR
    @35
    islvol2a.j
    latjcl
    syl3anc
    @31
    c.or
    cK
    c.le
    cS
    @9
    @35
    islvol2a.l
    islvol2a.j
    latleeqj2
    syl3anc
    @7
    @19
    @42
    @9
    cV
    wcel
    #
    wn
    #
    @7
    @0
    @1
    @2
    @4
    @46
    @24
    @41
    @25
    @27
    cA
    cP
    cQ
    cR
    c.or
    cK
    cV
    islvol2a.j
    islvol2a.a
    islvol2a.v
    3atnelvolN
    syl13anc
    @42
    @11
    @45
    @10
    @9
    cV
    eleq1
    notbid
    syl5ibrcom
    sylbid
    con2d
    3jcad
    @3
    @6
    @17
    @11
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cV
    islvol2a.l
    islvol2a.j
    islvol2a.a
    islvol2a.v
    lvoli2
    3expia
    impbid
end
