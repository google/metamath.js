include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cco1.mm"
include "co.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cur.mm"
include "wceq.mm"
include "ply1ring.mm"
include "adantr.mm"
include "wf.mm"
include "eqid.mm"
include "ply1sclf.mm"
include "cui.mm"
include "uc1pldg.mm"
include "ringinvcl.mm"
include "sylan2.mm"
include "ffvelrnd.mm"
include "uc1pcl.mm"
include "adantl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cn0.mm"
include "crlreg.mm"
include "simpl.mm"
include "wss.mm"
include "unitrrg.mm"
include "unitinvcl.mm"
include "sseldd.mm"
include "deg1mul3.mm"
include "uc1pdeg.mm"
include "eqeltrd.mm"
include "wb.mm"
include "deg1nn0clb.mm"
include "syldan.mm"
include "mpbird.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "fveq2d.mm"
include "coe1sclmul.mm"
include "fveq1d.mm"
include "cvv.mm"
include "nn0ex.mm"
include "a1i.mm"
include "fvexd.mm"
include "wfn.mm"
include "coe1f.mm"
include "ffn.mm"
include "3syl.mm"
include "eqidd.mm"
include "ofc1.mm"
include "mpdan.mm"
include "unitlinv.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "ismon1p.mm"
include "syl3anbrc.mm"

theorem uc1pmon1p
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cM: class M
  let cX: class X
  assume uc1pmon1p.c: |- C = ( Unic1p ` R )
  assume uc1pmon1p.m: |- M = ( Monic1p ` R )
  assume uc1pmon1p.p: |- P = ( Poly1 ` R )
  assume uc1pmon1p.t: |- .x. = ( .r ` P )
  assume uc1pmon1p.a: |- A = ( algSc ` P )
  assume uc1pmon1p.d: |- D = ( deg1 ` R )
  assume uc1pmon1p.i: |- I = ( invr ` R )


  assert |- ( ( R e. Ring /\ X e. C ) -> ( ( A ` ( I ` ( ( coe1 ` X ) ` ( D ` X ) ) ) ) .x. X ) e. M )

  proof
    cR
    crg
    wcel
    #
    cX
    cC
    wcel
    #
    wa
    #
    cX
    cD
    cfv
    #
    cX
    cco1
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    cA
    cfv
    #
    cX
    c.x
    co
    #
    cP
    cbs
    cfv
    #
    wcel
    #
    @8
    cP
    c0g
    cfv
    #
    wne
    #
    @8
    cD
    cfv
    #
    @8
    cco1
    cfv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    wceq
    @8
    cM
    wcel
    @2
    cP
    crg
    wcel
    #
    @7
    @9
    wcel
    cX
    @9
    wcel
    #
    @10
    @0
    @17
    @1
    cP
    cR
    uc1pmon1p.p
    ply1ring
    adantr
    @2
    cR
    cbs
    cfv
    #
    @9
    @6
    cA
    @0
    @19
    @9
    cA
    wf
    @1
    cA
    @9
    cP
    cR
    @19
    uc1pmon1p.p
    uc1pmon1p.a
    @19
    eqid
    #
    @9
    eqid
    #
    ply1sclf
    adantr
    @1
    @0
    @5
    cR
    cui
    cfv
    #
    wcel
    #
    @6
    @19
    wcel
    #
    cC
    cD
    cR
    @22
    cX
    uc1pmon1p.d
    @22
    eqid
    #
    uc1pmon1p.c
    uc1pldg
    #
    @19
    cR
    @22
    cI
    @5
    @25
    uc1pmon1p.i
    @20
    ringinvcl
    sylan2
    #
    ffvelrnd
    @1
    @18
    @0
    @9
    cC
    cP
    cR
    cX
    uc1pmon1p.p
    @21
    uc1pmon1p.c
    uc1pcl
    adantl
    #
    @9
    cP
    c.x
    @7
    cX
    @21
    uc1pmon1p.t
    ringcl
    syl3anc
    #
    @2
    @12
    @13
    cn0
    wcel
    #
    @2
    @13
    @3
    cn0
    @2
    @0
    @6
    cR
    crlreg
    cfv
    #
    wcel
    @18
    @13
    @3
    wceq
    @0
    @1
    simpl
    #
    @2
    @22
    @31
    @6
    @0
    @22
    @31
    wss
    @1
    cR
    @22
    @31
    @31
    eqid
    #
    @25
    unitrrg
    adantr
    @1
    @0
    @23
    @6
    @22
    wcel
    @26
    cR
    @22
    cI
    @5
    @25
    uc1pmon1p.i
    unitinvcl
    sylan2
    sseldd
    @28
    cA
    @9
    cD
    cP
    cR
    c.x
    @31
    @6
    cX
    uc1pmon1p.d
    uc1pmon1p.p
    @33
    @21
    uc1pmon1p.t
    uc1pmon1p.a
    deg1mul3
    syl3anc
    #
    cC
    cD
    cR
    cX
    uc1pmon1p.d
    uc1pmon1p.c
    uc1pdeg
    #
    eqeltrd
    @0
    @1
    @10
    @12
    @30
    wb
    @29
    @9
    cD
    cP
    cR
    @8
    @11
    uc1pmon1p.d
    uc1pmon1p.p
    @11
    eqid
    #
    @21
    deg1nn0clb
    syldan
    mpbird
    @2
    @15
    @3
    @14
    cfv
    @3
    cn0
    @6
    csn
    cxp
    @4
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    cfv
    #
    @16
    @2
    @13
    @3
    @14
    @34
    fveq2d
    @2
    @3
    @14
    @38
    @2
    @0
    @24
    @18
    @14
    @38
    wceq
    @32
    @27
    @28
    cA
    @9
    cP
    cR
    c.x
    @37
    @19
    @6
    cX
    uc1pmon1p.p
    @21
    @20
    uc1pmon1p.a
    uc1pmon1p.t
    @37
    eqid
    #
    coe1sclmul
    syl3anc
    fveq1d
    @2
    @39
    @6
    @5
    @37
    co
    #
    @16
    @2
    @3
    cn0
    wcel
    #
    @39
    @41
    wceq
    @35
    @2
    cn0
    @6
    @5
    @37
    @4
    cvv
    cvv
    @3
    cn0
    cvv
    wcel
    @2
    nn0ex
    a1i
    @2
    @5
    cI
    fvexd
    @2
    @18
    cn0
    @19
    @4
    wf
    @4
    cn0
    wfn
    @28
    @4
    @9
    cP
    cR
    cX
    @19
    @4
    eqid
    @21
    uc1pmon1p.p
    @20
    coe1f
    cn0
    @19
    @4
    ffn
    3syl
    @2
    @42
    wa
    @5
    eqidd
    ofc1
    mpdan
    @1
    @0
    @23
    @41
    @16
    wceq
    @26
    cR
    @37
    @22
    @16
    cI
    @5
    @25
    uc1pmon1p.i
    @40
    @16
    eqid
    #
    unitlinv
    sylan2
    eqtrd
    3eqtrd
    @9
    cD
    cP
    cR
    @16
    @8
    cM
    @11
    uc1pmon1p.p
    @21
    @36
    uc1pmon1p.d
    uc1pmon1p.m
    @43
    ismon1p
    syl3anbrc
end
