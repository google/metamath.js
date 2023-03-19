include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "clln.mm"
include "wrex.mm"
include "co.mm"
include "wn.mm"
include "cbs.mm"
include "simpr1.mm"
include "wb.mm"
include "eqid.mm"
include "islpln.mm"
include "adantr.mm"
include "mpbid.mm"
include "simprd.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "notbid.mm"
include "wne.mm"
include "cplt.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llnnlt.mm"
include "syl3anc.mm"
include "llnbase.mm"
include "syl.mm"
include "simpl21.mm"
include "lplnbase.mm"
include "simpl3r.mm"
include "cvrlt.mm"
include "cpo.mm"
include "hlpos.mm"
include "hlatjcl.mm"
include "pltletr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp23.mm"
include "llnnleat.mm"
include "simp21.mm"
include "simp3r.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "pltle.mm"
include "syld.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "mtbird.mm"
include "pm2.61ne.mm"
include "3exp.mm"
include "exp4a.mm"
include "imp.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem lplnnle2at
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vy: setvar y
  assume lplnnle2at.l: |- .<_ = ( le ` K )
  assume lplnnle2at.j: |- .\/ = ( join ` K )
  assume lplnnle2at.a: |- A = ( Atoms ` K )
  assume lplnnle2at.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ ( X e. P /\ Q e. A /\ R e. A ) ) -> -. X .<_ ( Q .\/ R ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
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
    wa
    #
    vy
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vy
    cK
    clln
    cfv
    #
    wrex
    #
    cX
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @5
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @5
    @1
    @15
    @10
    wa
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @16
    wb
    @4
    vy
    chlt
    @14
    @7
    cP
    cK
    @9
    cX
    @14
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    lplnnle2at.p
    islpln
    adantr
    mpbid
    simprd
    @5
    @8
    @13
    vy
    @9
    @0
    @4
    @6
    @9
    wcel
    #
    @8
    @13
    wi
    wi
    @0
    @4
    @20
    @8
    @13
    @0
    @4
    @20
    @8
    wa
    #
    @13
    @0
    @4
    @21
    w3a
    #
    @13
    cX
    cR
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    cQ
    cR
    cQ
    cR
    wceq
    #
    @12
    @24
    @25
    @11
    @23
    cX
    c.le
    cQ
    cR
    cR
    c.or
    oveq1
    breq2d
    notbid
    @22
    cQ
    cR
    wne
    #
    wa
    #
    @12
    @6
    @11
    cK
    cplt
    cfv
    #
    wbr
    #
    @27
    @0
    @20
    @11
    @9
    wcel
    #
    @29
    wn
    @0
    @4
    @21
    @26
    simpl1
    #
    @20
    @8
    @0
    @4
    @26
    simpl3l
    #
    @27
    @0
    @2
    @3
    @26
    @30
    @31
    @1
    @2
    @3
    @0
    @21
    @26
    simpl22
    #
    @1
    @2
    @3
    @0
    @21
    @26
    simpl23
    #
    @22
    @26
    simpr
    cA
    cQ
    cR
    c.or
    cK
    @9
    lplnnle2at.j
    lplnnle2at.a
    @19
    llni2
    syl31anc
    @28
    cK
    @9
    @6
    @11
    @28
    eqid
    #
    @19
    llnnlt
    syl3anc
    @27
    @6
    cX
    @28
    wbr
    #
    @12
    @29
    @27
    @0
    @6
    @14
    wcel
    #
    @15
    @8
    @36
    @31
    @27
    @20
    @37
    @32
    @14
    cK
    @9
    @6
    @17
    @19
    llnbase
    #
    syl
    #
    @27
    @1
    @15
    @1
    @2
    @3
    @0
    @21
    @26
    simpl21
    @14
    cP
    cK
    cX
    @17
    lplnnle2at.p
    lplnbase
    #
    syl
    #
    @20
    @8
    @0
    @4
    @26
    simpl3r
    chlt
    @14
    @7
    @28
    cK
    @6
    cX
    @17
    @35
    @18
    cvrlt
    #
    syl31anc
    @27
    cK
    cpo
    wcel
    #
    @37
    @15
    @11
    @14
    wcel
    #
    @36
    @12
    wa
    @29
    wi
    @27
    @0
    @43
    @31
    cK
    hlpos
    #
    syl
    @39
    @41
    @27
    @0
    @2
    @3
    @44
    @31
    @33
    @34
    cA
    @14
    c.or
    cK
    cQ
    cR
    @17
    lplnnle2at.j
    lplnnle2at.a
    hlatjcl
    syl3anc
    @14
    @28
    cK
    c.le
    @6
    cX
    @11
    @17
    lplnnle2at.l
    @35
    pltletr
    syl13anc
    mpand
    mtod
    @22
    @24
    cX
    cR
    c.le
    wbr
    #
    @22
    @46
    @6
    cR
    c.le
    wbr
    #
    @22
    @0
    @20
    @3
    @47
    wn
    @0
    @4
    @21
    simp1
    #
    @0
    @4
    @20
    @8
    simp3l
    #
    @0
    @1
    @2
    @3
    @21
    simp23
    #
    cA
    cR
    cK
    c.le
    @9
    @6
    lplnnle2at.l
    lplnnle2at.a
    @19
    llnnleat
    syl3anc
    @22
    @46
    @6
    cR
    @28
    wbr
    #
    @47
    @22
    @36
    @46
    @51
    @22
    @0
    @37
    @15
    @8
    @36
    @48
    @22
    @20
    @37
    @49
    @38
    syl
    #
    @22
    @1
    @15
    @0
    @1
    @2
    @3
    @21
    simp21
    @40
    syl
    #
    @0
    @4
    @20
    @8
    simp3r
    @42
    syl31anc
    @22
    @43
    @37
    @15
    cR
    @14
    wcel
    #
    @36
    @46
    wa
    @51
    wi
    @0
    @4
    @43
    @21
    @45
    3ad2ant1
    @52
    @53
    @22
    @3
    @54
    @50
    cA
    @14
    cR
    cK
    @17
    lplnnle2at.a
    atbase
    syl
    @14
    @28
    cK
    c.le
    @6
    cX
    cR
    @17
    lplnnle2at.l
    @35
    pltletr
    syl13anc
    mpand
    @22
    @0
    @20
    @3
    @51
    @47
    wi
    @48
    @49
    @50
    chlt
    @9
    cA
    @28
    cK
    c.le
    @6
    cR
    lplnnle2at.l
    @35
    pltle
    syl3anc
    syld
    mtod
    @22
    @23
    cR
    cX
    c.le
    @22
    @0
    @3
    @23
    cR
    wceq
    @48
    @50
    cA
    c.or
    cK
    cR
    lplnnle2at.j
    lplnnle2at.a
    hlatjidm
    syl2anc
    breq2d
    mtbird
    pm2.61ne
    3exp
    exp4a
    imp
    rexlimdv
    mpd
end
