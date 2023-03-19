include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wb.mm"
include "oveq1.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "eqcoms.mm"
include "simp3.mm"
include "simp1.mm"
include "simp21.mm"
include "simp3l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "3ad2ant1.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "simp3r.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simpl.mm"
include "syl6bir.mm"
include "adantr.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl3r.mm"
include "simpl3l.mm"
include "simpr.mm"
include "hlatexchb1.mm"
include "syl131anc.mm"
include "sylibd.mm"
include "3impia.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "3expia.mm"
include "simp23.mm"
include "necomd.mm"
include "syl5ib.mm"
include "sylbird.mm"
include "syld.mm"
include "pm2.61ne.mm"
include "latref.mm"
include "syl2anc.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem ps-1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume ps1.l: |- .<_ = ( le ` K )
  assume ps1.j: |- .\/ = ( join ` K )
  assume ps1.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ P =/= Q ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .<_ ( R .\/ S ) <-> ( P .\/ Q ) = ( R .\/ S ) ) )

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
    cP
    cQ
    wne
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
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cR
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    @10
    wceq
    #
    @8
    @11
    @12
    wi
    #
    @9
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    @14
    wceq
    #
    wi
    #
    cP
    cR
    @13
    @17
    wb
    cR
    cP
    cR
    cP
    wceq
    #
    @11
    @15
    @12
    @16
    @18
    @10
    @14
    @9
    c.le
    cR
    cP
    cS
    c.or
    oveq1
    #
    breq2d
    @18
    @10
    @14
    @9
    @19
    eqeq2d
    imbi12d
    eqcoms
    @8
    cP
    cR
    wne
    #
    @11
    @12
    @8
    @20
    @11
    w3a
    #
    @9
    cP
    cR
    c.or
    co
    #
    @10
    @8
    @20
    @11
    @9
    @22
    wceq
    #
    @8
    @20
    wa
    #
    @11
    @9
    @22
    c.le
    wbr
    #
    @23
    @8
    @20
    @11
    @25
    @21
    @9
    @10
    @22
    c.le
    @8
    @20
    @11
    simp3
    @21
    @22
    cR
    cP
    c.or
    co
    #
    @10
    @8
    @20
    @22
    @26
    wceq
    #
    @11
    @8
    @0
    @1
    @5
    @27
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    cA
    c.or
    cK
    cP
    cR
    ps1.j
    ps1.a
    hlatjcom
    syl3anc
    3ad2ant1
    @8
    @20
    @11
    @26
    @10
    wceq
    #
    @24
    @11
    cP
    @10
    c.le
    wbr
    #
    @31
    @8
    @11
    @32
    wi
    @20
    @8
    @11
    @32
    cQ
    @10
    c.le
    wbr
    #
    wa
    #
    @32
    @8
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
    @36
    wcel
    #
    @10
    @36
    wcel
    #
    @34
    @11
    wb
    @0
    @4
    @35
    @7
    cK
    hllat
    3ad2ant1
    #
    @8
    @1
    @37
    @29
    cA
    @36
    cP
    cK
    @36
    eqid
    #
    ps1.a
    atbase
    syl
    #
    @8
    @2
    @38
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    cA
    @36
    cQ
    cK
    @41
    ps1.a
    atbase
    syl
    #
    @8
    @0
    @5
    @6
    @39
    @28
    @30
    @0
    @4
    @5
    @6
    simp3r
    #
    cA
    @36
    c.or
    cK
    cR
    cS
    @41
    ps1.j
    ps1.a
    hlatjcl
    syl3anc
    @36
    c.or
    cK
    c.le
    cP
    cQ
    @10
    @41
    ps1.l
    ps1.j
    latjle12
    syl13anc
    @32
    @33
    simpl
    syl6bir
    adantr
    @24
    @0
    @1
    @6
    @5
    @20
    @32
    @31
    wb
    @0
    @4
    @7
    @20
    simpl1
    @1
    @2
    @3
    @0
    @7
    @20
    simpl21
    @5
    @6
    @0
    @4
    @20
    simpl3r
    @5
    @6
    @0
    @4
    @20
    simpl3l
    @8
    @20
    simpr
    cA
    cP
    cS
    cR
    c.or
    cK
    c.le
    ps1.l
    ps1.j
    ps1.a
    hlatexchb1
    syl131anc
    sylibd
    3impia
    eqtrd
    #
    breqtrrd
    3expia
    @8
    @25
    @23
    wi
    @20
    @8
    @25
    cP
    @22
    c.le
    wbr
    #
    cQ
    @22
    c.le
    wbr
    #
    wa
    #
    @23
    @8
    @35
    @37
    @38
    @22
    @36
    wcel
    #
    @49
    @25
    wb
    @40
    @42
    @44
    @8
    @0
    @1
    @5
    @50
    @28
    @29
    @30
    cA
    @36
    c.or
    cK
    cP
    cR
    @41
    ps1.j
    ps1.a
    hlatjcl
    syl3anc
    @36
    c.or
    cK
    c.le
    cP
    cQ
    @22
    @41
    ps1.l
    ps1.j
    latjle12
    syl13anc
    @49
    @48
    @8
    @23
    @47
    @48
    simpr
    @8
    @0
    @2
    @5
    @1
    cQ
    cP
    wne
    #
    @48
    @23
    wb
    @28
    @43
    @30
    @29
    @8
    cP
    cQ
    @0
    @1
    @2
    @3
    @7
    simp23
    necomd
    #
    cA
    cQ
    cR
    cP
    c.or
    cK
    c.le
    ps1.l
    ps1.j
    ps1.a
    hlatexchb1
    syl131anc
    syl5ib
    sylbird
    adantr
    syld
    3impia
    @46
    eqtrd
    3expia
    @8
    @15
    cQ
    @14
    c.le
    wbr
    #
    @16
    @8
    @15
    cP
    @14
    c.le
    wbr
    #
    @53
    wa
    #
    @53
    @8
    @35
    @37
    @38
    @14
    @36
    wcel
    #
    @55
    @15
    wb
    @40
    @42
    @44
    @8
    @0
    @1
    @6
    @56
    @28
    @29
    @45
    cA
    @36
    c.or
    cK
    cP
    cS
    @41
    ps1.j
    ps1.a
    hlatjcl
    syl3anc
    @36
    c.or
    cK
    c.le
    cP
    cQ
    @14
    @41
    ps1.l
    ps1.j
    latjle12
    syl13anc
    @54
    @53
    simpr
    syl6bir
    @8
    @0
    @2
    @6
    @1
    @51
    @53
    @16
    wb
    @28
    @43
    @45
    @29
    @52
    cA
    cQ
    cS
    cP
    c.or
    cK
    c.le
    ps1.l
    ps1.j
    ps1.a
    hlatexchb1
    syl131anc
    sylibd
    pm2.61ne
    @8
    @9
    @9
    c.le
    wbr
    #
    @12
    @11
    @8
    @35
    @9
    @36
    wcel
    #
    @57
    @40
    @8
    @0
    @1
    @2
    @58
    @28
    @29
    @43
    cA
    @36
    c.or
    cK
    cP
    cQ
    @41
    ps1.j
    ps1.a
    hlatjcl
    syl3anc
    @36
    cK
    c.le
    @9
    @41
    ps1.l
    latref
    syl2anc
    @9
    @10
    @9
    c.le
    breq2
    syl5ibcom
    impbid
end
