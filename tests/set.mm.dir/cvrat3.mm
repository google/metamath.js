include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccvr.mm"
include "cfv.mm"
include "wi.mm"
include "wb.mm"
include "eqid.mm"
include "cvr1.mm"
include "3adant3r2.mm"
include "biimpa.mm"
include "adantrr.mm"
include "wceq.mm"
include "clat.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr2.mm"
include "atbase.mm"
include "syl.mm"
include "simpr3.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simpr1.mm"
include "latjass.mm"
include "syl13anc.mm"
include "eqtr4d.mm"
include "latjcl.mm"
include "latjlej2.mm"
include "imp.mm"
include "eqbrtrd.mm"
include "latjidm.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "simpl.mm"
include "hlatlej2.mm"
include "mpd.mm"
include "latasymb.mm"
include "mpbi2and.mm"
include "breq2d.mm"
include "adantrl.mm"
include "mpbird.mm"
include "ex.mm"
include "cvrexch.mm"
include "sylibrd.mm"
include "latmcl.mm"
include "cvrat2.mm"
include "3expia.mm"
include "expdimp.mm"
include "syld.mm"
include "exp4b.mm"
include "3impd.mm"

theorem cvrat3
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  assume cvrat3.b: |- B = ( Base ` K )
  assume cvrat3.l: |- .<_ = ( le ` K )
  assume cvrat3.j: |- .\/ = ( join ` K )
  assume cvrat3.m: |- ./\ = ( meet ` K )
  assume cvrat3.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) ) -> ( ( P =/= Q /\ -. Q .<_ X /\ P .<_ ( X .\/ Q ) ) -> ( X ./\ ( P .\/ Q ) ) e. A ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
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
    wa
    #
    cP
    cQ
    wne
    #
    cQ
    cX
    c.le
    wbr
    wn
    #
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cX
    cP
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cA
    wcel
    #
    @5
    @6
    @7
    @9
    @12
    @5
    @6
    wa
    @7
    @9
    wa
    #
    @11
    @10
    cK
    ccvr
    cfv
    #
    wbr
    #
    @12
    @5
    @13
    @15
    wi
    @6
    @5
    @13
    cX
    cX
    @10
    c.or
    co
    #
    @14
    wbr
    #
    @15
    @5
    @13
    @17
    @5
    @13
    wa
    @17
    cX
    @8
    @14
    wbr
    #
    @5
    @7
    @18
    @9
    @5
    @7
    @18
    @0
    @1
    @3
    @7
    @18
    wb
    @2
    cA
    cB
    @14
    cQ
    c.or
    cK
    c.le
    cX
    cvrat3.b
    cvrat3.l
    cvrat3.j
    @14
    eqid
    #
    cvrat3.a
    cvr1
    3adant3r2
    biimpa
    adantrr
    @5
    @9
    @17
    @18
    wb
    @7
    @5
    @9
    wa
    #
    @16
    @8
    cX
    @14
    @20
    @16
    @8
    c.le
    wbr
    #
    @8
    @16
    c.le
    wbr
    #
    @16
    @8
    wceq
    #
    @20
    @16
    @8
    @8
    c.or
    co
    #
    @8
    c.le
    @20
    @16
    @8
    cP
    c.or
    co
    #
    @24
    c.le
    @5
    @16
    @25
    wceq
    @9
    @5
    @16
    cX
    cQ
    cP
    c.or
    co
    #
    c.or
    co
    #
    @25
    @5
    @10
    @26
    cX
    c.or
    @5
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @10
    @26
    wceq
    @0
    @28
    @4
    cK
    hllat
    adantr
    #
    @5
    @2
    @29
    @0
    @1
    @2
    @3
    simpr2
    #
    cA
    cB
    cP
    cK
    cvrat3.b
    cvrat3.a
    atbase
    syl
    #
    @5
    @3
    @30
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    cB
    cQ
    cK
    cvrat3.b
    cvrat3.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cP
    cQ
    cvrat3.b
    cvrat3.j
    latjcom
    syl3anc
    oveq2d
    @5
    @28
    @1
    @30
    @29
    @25
    @27
    wceq
    @31
    @0
    @1
    @2
    @3
    simpr1
    #
    @35
    @33
    cB
    c.or
    cK
    cX
    cQ
    cP
    cvrat3.b
    cvrat3.j
    latjass
    syl13anc
    eqtr4d
    adantr
    @5
    @9
    @25
    @24
    c.le
    wbr
    #
    @5
    @28
    @29
    @8
    cB
    wcel
    #
    @38
    @9
    @37
    wi
    @31
    @33
    @5
    @28
    @1
    @30
    @38
    @31
    @36
    @35
    cB
    c.or
    cK
    cX
    cQ
    cvrat3.b
    cvrat3.j
    latjcl
    syl3anc
    #
    @39
    cB
    c.or
    cK
    c.le
    cP
    @8
    @8
    cvrat3.b
    cvrat3.l
    cvrat3.j
    latjlej2
    syl13anc
    imp
    eqbrtrd
    @5
    @24
    @8
    wceq
    #
    @9
    @5
    @28
    @38
    @40
    @31
    @39
    cB
    c.or
    cK
    @8
    cvrat3.b
    cvrat3.j
    latjidm
    syl2anc
    adantr
    breqtrd
    @5
    @22
    @9
    @5
    cQ
    @10
    c.le
    wbr
    #
    @22
    @5
    @0
    @2
    @3
    @41
    @0
    @4
    simpl
    #
    @32
    @34
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cvrat3.l
    cvrat3.j
    cvrat3.a
    hlatlej2
    syl3anc
    @5
    @28
    @30
    @10
    cB
    wcel
    #
    @1
    @41
    @22
    wi
    @31
    @35
    @5
    @28
    @29
    @30
    @43
    @31
    @33
    @35
    cB
    c.or
    cK
    cP
    cQ
    cvrat3.b
    cvrat3.j
    latjcl
    syl3anc
    #
    @36
    cB
    c.or
    cK
    c.le
    cQ
    @10
    cX
    cvrat3.b
    cvrat3.l
    cvrat3.j
    latjlej2
    syl13anc
    mpd
    adantr
    @5
    @21
    @22
    wa
    @23
    wb
    #
    @9
    @5
    @28
    @16
    cB
    wcel
    #
    @38
    @45
    @31
    @5
    @28
    @1
    @43
    @46
    @31
    @36
    @44
    cB
    c.or
    cK
    cX
    @10
    cvrat3.b
    cvrat3.j
    latjcl
    syl3anc
    @39
    cB
    cK
    c.le
    @16
    @8
    cvrat3.b
    cvrat3.l
    latasymb
    syl3anc
    adantr
    mpbi2and
    breq2d
    adantrl
    mpbird
    ex
    @5
    @0
    @1
    @43
    @15
    @17
    wb
    @42
    @36
    @44
    cB
    @14
    c.or
    cK
    c.an
    cX
    @10
    cvrat3.b
    cvrat3.j
    cvrat3.m
    @19
    cvrexch
    syl3anc
    sylibrd
    adantr
    @5
    @6
    @15
    @12
    @5
    @0
    @11
    cB
    wcel
    #
    @2
    @3
    @6
    @15
    wa
    #
    @12
    wi
    @42
    @5
    @28
    @1
    @43
    @47
    @31
    @36
    @44
    cB
    cK
    c.an
    cX
    @10
    cvrat3.b
    cvrat3.m
    latmcl
    syl3anc
    @32
    @34
    @0
    @47
    @2
    @3
    w3a
    @48
    @12
    cA
    cB
    @14
    cP
    cQ
    c.or
    cK
    @11
    cvrat3.b
    cvrat3.j
    @19
    cvrat3.a
    cvrat2
    3expia
    syl13anc
    expdimp
    syld
    exp4b
    3impd
end
