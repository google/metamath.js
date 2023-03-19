include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "c0p.mm"
include "wceq.mm"
include "wo.mm"
include "cdgr.mm"
include "ccoe.mm"
include "cc0.mm"
include "caddc.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "dgrcl.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "syl.mm"
include "fveq2.mm"
include "coe0.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "eqid.mm"
include "coemulhi.mm"
include "cc.mm"
include "wf.mm"
include "coef3.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "adantl.mm"
include "mul0ord.mm"
include "bitrd.mm"
include "sylibd.mm"
include "wb.mm"
include "dgreq0.mm"
include "orbi12d.mm"
include "sylibrd.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "plyf.mm"
include "0cnd.mm"
include "cv.mm"
include "mul02.mm"
include "caofid2.mm"
include "id.mm"
include "df-0p.mm"
include "oveq1d.mm"
include "mul01.mm"
include "caofid1.mm"
include "oveq2d.mm"
include "jaod.mm"
include "eqeq2i.mm"
include "syl6ibr.mm"
include "impbid.mm"

theorem plymul0or
  let cS: class S
  let cF: class F
  let cG: class G
  let cA: class A
  let vx: setvar x
  let cV: class V


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( ( F oF x. G ) = 0p <-> ( F = 0p \/ G = 0p ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cmul
    cof
    #
    co
    #
    c0p
    wceq
    #
    cF
    c0p
    wceq
    #
    cG
    c0p
    wceq
    #
    wo
    #
    @3
    @6
    cF
    cdgr
    cfv
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    cG
    cdgr
    cfv
    #
    cG
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    wo
    #
    @9
    @3
    @6
    @10
    @14
    caddc
    co
    #
    @5
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @18
    @3
    @22
    @6
    @19
    cn0
    cc0
    csn
    #
    cxp
    #
    cfv
    #
    cc0
    wceq
    #
    @3
    @19
    cn0
    wcel
    #
    @26
    @1
    @10
    cn0
    wcel
    #
    @14
    cn0
    wcel
    #
    @27
    @2
    cS
    cF
    dgrcl
    #
    cS
    cG
    dgrcl
    #
    @10
    @14
    nn0addcl
    syl2an
    cn0
    cc0
    @19
    c0ex
    fvconst2
    syl
    @6
    @21
    @25
    cc0
    @6
    @19
    @20
    @24
    @6
    @20
    c0p
    ccoe
    cfv
    @24
    @5
    c0p
    ccoe
    fveq2
    coe0
    syl6eq
    fveq1d
    eqeq1d
    syl5ibrcom
    @3
    @22
    @12
    @16
    cmul
    co
    #
    cc0
    wceq
    @18
    @3
    @21
    @32
    cc0
    @11
    @15
    cS
    cF
    cG
    @10
    @14
    @11
    eqid
    #
    @15
    eqid
    #
    @10
    eqid
    #
    @14
    eqid
    #
    coemulhi
    eqeq1d
    @3
    @12
    @16
    @3
    cn0
    cc
    @10
    @11
    @1
    cn0
    cc
    @11
    wf
    @2
    @11
    cS
    cF
    @33
    coef3
    adantr
    @1
    @28
    @2
    @30
    adantr
    ffvelrnd
    @3
    cn0
    cc
    @14
    @15
    @2
    cn0
    cc
    @15
    wf
    @1
    @15
    cS
    cG
    @34
    coef3
    adantl
    @2
    @29
    @1
    @31
    adantl
    ffvelrnd
    mul0ord
    bitrd
    sylibd
    @3
    @7
    @13
    @8
    @17
    @1
    @7
    @13
    wb
    @2
    @11
    cS
    cF
    @10
    @35
    @33
    dgreq0
    adantr
    @2
    @8
    @17
    wb
    @1
    @15
    cS
    cG
    @14
    @36
    @34
    dgreq0
    adantl
    orbi12d
    sylibrd
    @3
    @9
    @5
    cc
    @23
    cxp
    #
    wceq
    #
    @6
    @3
    @7
    @38
    @8
    @3
    @38
    @7
    @37
    cG
    @4
    co
    #
    @37
    wceq
    @3
    vx
    cc
    cc0
    cc0
    cmul
    cc
    cG
    cvv
    cc
    cc
    cc
    cvv
    wcel
    @3
    cnex
    a1i
    #
    @2
    cc
    cc
    cG
    wf
    @1
    cS
    cG
    plyf
    adantl
    @3
    0cnd
    #
    @41
    vx
    cv
    #
    cc
    wcel
    #
    cc0
    @42
    cmul
    co
    cc0
    wceq
    @3
    @42
    mul02
    adantl
    caofid2
    @7
    @5
    @39
    @37
    @7
    cF
    @37
    cG
    @4
    @7
    cF
    c0p
    @37
    @7
    id
    df-0p
    syl6eq
    oveq1d
    eqeq1d
    syl5ibrcom
    @3
    @38
    @8
    cF
    @37
    @4
    co
    #
    @37
    wceq
    @3
    vx
    cc
    cc0
    cc0
    cmul
    cc
    cF
    cvv
    cc
    cc
    @40
    @1
    cc
    cc
    cF
    wf
    @2
    cS
    cF
    plyf
    adantr
    @41
    @41
    @43
    @42
    cc0
    cmul
    co
    cc0
    wceq
    @3
    @42
    mul01
    adantl
    caofid1
    @8
    @5
    @44
    @37
    @8
    cG
    @37
    cF
    @4
    @8
    cG
    c0p
    @37
    @8
    id
    df-0p
    syl6eq
    oveq2d
    eqeq1d
    syl5ibrcom
    jaod
    c0p
    @37
    @5
    df-0p
    eqeq2i
    syl6ibr
    impbid
end
