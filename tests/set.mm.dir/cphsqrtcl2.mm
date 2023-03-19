include "ccph.mm"
include "wcel.mm"
include "cneg.mm"
include "crp.mm"
include "wn.mm"
include "w3a.mm"
include "csqrt.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "sqrt0.mm"
include "fveq2.mm"
include "id.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "simpl2.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cabs.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "cc.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "wss.mm"
include "simpl1.mm"
include "cphsubrg.mm"
include "syl.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "cphabscl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "abscld.mm"
include "absge0d.mm"
include "cphsqrtcl.mm"
include "syl13anc.mm"
include "cnfldadd.mm"
include "subrgacl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "cmin.mm"
include "recnd.mm"
include "subnegd.mm"
include "eqeq1d.mm"
include "negcld.mm"
include "subeq0ad.mm"
include "bitr3d.mm"
include "absrpcl.mm"
include "sylancom.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "necon3bd.mm"
include "mpd.mm"
include "absne0d.mm"
include "cphdivcl.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "c2.mm"
include "cexp.mm"
include "cre.mm"
include "ci.mm"
include "wnel.mm"
include "eqid.mm"
include "sqreulem.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "df-nel.mm"
include "sylib.mm"
include "eqsqrtd.mm"
include "eqeltrrd.mm"
include "pm2.61dane.mm"

theorem cphsqrtcl2
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ A e. K /\ -. -u A e. RR+ ) -> ( sqrt ` A ) e. K )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    #
    cA
    cneg
    #
    crp
    wcel
    #
    wn
    #
    w3a
    #
    cA
    csqrt
    cfv
    #
    cK
    wcel
    cA
    cc0
    @5
    cA
    cc0
    wceq
    #
    wa
    @6
    cA
    cK
    @7
    @6
    cA
    wceq
    @5
    @7
    cc0
    csqrt
    cfv
    cc0
    @6
    cA
    sqrt0
    cA
    cc0
    csqrt
    fveq2
    @7
    id
    3eqtr4a
    adantl
    @0
    @1
    @4
    @7
    simpl2
    eqeltrd
    @5
    cA
    cc0
    wne
    #
    wa
    #
    cA
    cabs
    cfv
    #
    csqrt
    cfv
    #
    @10
    cA
    caddc
    co
    #
    @12
    cabs
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    @6
    cK
    @9
    @15
    cA
    @9
    cK
    cc
    @15
    @9
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cK
    cc
    wss
    @9
    @0
    @16
    @0
    @1
    @4
    @8
    simpl1
    #
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsubrg
    syl
    #
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    @9
    @16
    @11
    cK
    wcel
    #
    @14
    cK
    wcel
    #
    @15
    cK
    wcel
    @18
    @9
    @0
    @10
    cK
    wcel
    #
    @10
    cr
    wcel
    cc0
    @10
    cle
    wbr
    @20
    @17
    @9
    @0
    @1
    @22
    @17
    @0
    @1
    @4
    @8
    simpl2
    #
    cA
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphabscl
    syl2anc
    #
    @9
    cA
    @9
    cK
    cc
    cA
    @19
    @23
    sseldd
    #
    abscld
    #
    @9
    cA
    @25
    absge0d
    @10
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsqrtcl
    syl13anc
    @9
    @0
    @12
    cK
    wcel
    #
    @13
    cK
    wcel
    #
    @13
    cc0
    wne
    @21
    @17
    @9
    @16
    @22
    @1
    @27
    @18
    @24
    @23
    cK
    caddc
    ccnfld
    @10
    cA
    cnfldadd
    subrgacl
    syl3anc
    #
    @9
    @0
    @27
    @28
    @17
    @29
    @12
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphabscl
    syl2anc
    @9
    @12
    @9
    cK
    cc
    @12
    @19
    @29
    sseldd
    @9
    @4
    @12
    cc0
    wne
    #
    @0
    @1
    @4
    @8
    simpl3
    @9
    @3
    @12
    cc0
    @9
    @12
    cc0
    wceq
    #
    @10
    @2
    wceq
    #
    @3
    @9
    @10
    @2
    cmin
    co
    #
    cc0
    wceq
    @31
    @32
    @9
    @33
    @12
    cc0
    @9
    @10
    cA
    @9
    @10
    @26
    recnd
    #
    @25
    subnegd
    eqeq1d
    @9
    @10
    @2
    @34
    @9
    cA
    @25
    negcld
    subeq0ad
    bitr3d
    @9
    @10
    crp
    wcel
    #
    @32
    @3
    @5
    @8
    cA
    cc
    wcel
    #
    @35
    @25
    cA
    absrpcl
    sylancom
    @10
    @2
    crp
    eleq1
    syl5ibcom
    sylbid
    necon3bd
    mpd
    #
    absne0d
    @12
    @13
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphdivcl
    syl13anc
    cK
    ccnfld
    cmul
    @11
    @14
    cnfldmul
    subrgmcl
    syl3anc
    #
    sseldd
    @25
    @9
    @15
    c2
    cexp
    co
    cA
    wceq
    #
    cc0
    @15
    cre
    cfv
    cle
    wbr
    #
    ci
    @15
    cmul
    co
    #
    crp
    wnel
    #
    @9
    @36
    @30
    @39
    @40
    @42
    w3a
    @25
    @37
    cA
    @15
    @15
    eqid
    sqreulem
    syl2anc
    #
    simp1d
    @9
    @39
    @40
    @42
    @43
    simp2d
    @9
    @42
    @41
    crp
    wcel
    wn
    @9
    @39
    @40
    @42
    @43
    simp3d
    @41
    crp
    df-nel
    sylib
    eqsqrtd
    @38
    eqeltrrd
    pm2.61dane
end
