include "ccph.mm"
include "wcel.mm"
include "ci.mm"
include "w3a.mm"
include "cneg.mm"
include "crp.mm"
include "csqrt.mm"
include "cfv.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "wss.mm"
include "simpl1.mm"
include "cphsubrg.mm"
include "syl.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "simpl3.mm"
include "sseldd.mm"
include "negnegd.mm"
include "fveq2d.mm"
include "cr.mm"
include "rpre.mm"
include "adantl.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rpge0.mm"
include "sqrtnegd.mm"
include "eqtr3d.mm"
include "simpl2.mm"
include "cminusg.mm"
include "wceq.mm"
include "cnfldneg.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "eqid.mm"
include "subginvcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "cphsqrtcl.mm"
include "syl13anc.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "wi.mm"
include "cphsqrtcl2.mm"
include "3expia.mm"
include "3adant2.mm"
include "pm2.61d.mm"

theorem cphsqrtcl3
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ _i e. K /\ A e. K ) -> ( sqrt ` A ) e. K )

  proof
    cW
    ccph
    wcel
    #
    ci
    cK
    wcel
    #
    cA
    cK
    wcel
    #
    w3a
    #
    cA
    cneg
    #
    crp
    wcel
    #
    cA
    csqrt
    cfv
    #
    cK
    wcel
    #
    @3
    @5
    @7
    @3
    @5
    wa
    #
    @6
    ci
    @4
    csqrt
    cfv
    #
    cmul
    co
    #
    cK
    @8
    @4
    cneg
    #
    csqrt
    cfv
    @6
    @10
    @8
    @11
    cA
    csqrt
    @8
    cA
    @8
    cK
    cc
    cA
    @8
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cK
    cc
    wss
    @8
    @0
    @12
    @0
    @1
    @2
    @5
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
    @0
    @1
    @2
    @5
    simpl3
    #
    sseldd
    #
    negnegd
    fveq2d
    @8
    @4
    @5
    @4
    cr
    wcel
    #
    @3
    @4
    rpre
    adantl
    #
    @5
    cc0
    @4
    cle
    wbr
    #
    @3
    @4
    rpge0
    adantl
    #
    sqrtnegd
    eqtr3d
    @8
    @12
    @1
    @9
    cK
    wcel
    #
    @10
    cK
    wcel
    @14
    @0
    @1
    @2
    @5
    simpl2
    @8
    @0
    @4
    cK
    wcel
    @17
    @19
    @21
    @13
    @8
    cA
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    @4
    cK
    @8
    cA
    cc
    wcel
    @23
    @4
    wceq
    @16
    cA
    cnfldneg
    syl
    @8
    cK
    ccnfld
    csubg
    cfv
    wcel
    #
    @2
    @23
    cK
    wcel
    @8
    @12
    @24
    @14
    cK
    ccnfld
    subrgsubg
    syl
    @15
    cK
    ccnfld
    @22
    cA
    @22
    eqid
    subginvcl
    syl2anc
    eqeltrrd
    @18
    @20
    @4
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsqrtcl
    syl13anc
    cK
    ccnfld
    cmul
    ci
    @9
    cnfldmul
    subrgmcl
    syl3anc
    eqeltrd
    ex
    @0
    @2
    @5
    wn
    #
    @7
    wi
    @1
    @0
    @2
    @25
    @7
    cA
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsqrtcl2
    3expia
    3adant2
    pm2.61d
end
