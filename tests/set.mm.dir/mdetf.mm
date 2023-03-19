include "ccrg.mm"
include "wcel.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "wa.mm"
include "crg.mm"
include "ccmn.mm"
include "crngring.mm"
include "adantr.mm"
include "ringcmn.mm"
include "syl.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "adantl.mm"
include "simpld.mm"
include "eqid.mm"
include "symgbasfi.mm"
include "ad2antrr.mm"
include "cmhm.mm"
include "wf.mm"
include "zrhpsgnmhm.mm"
include "syl2anc.mm"
include "mgpbas.mm"
include "mhmf.mm"
include "ffvelrnda.mm"
include "crngmgp.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "ad3antlr.mm"
include "elmapi.mm"
include "symgbasf.mm"
include "simpr.mm"
include "fovrnd.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "mdetfval.mm"
include "fmptd.mm"

theorem mdetf
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cK: class K
  let cN: class N
  let vp: setvar p
  let vc: setvar c
  let vm: setvar m
  assume mdetf.d: |- D = ( N maDet R )
  assume mdetf.a: |- A = ( N Mat R )
  assume mdetf.b: |- B = ( Base ` A )
  assume mdetf.k: |- K = ( Base ` R )


  assert |- ( R e. CRing -> D : B --> K )

  proof
    cR
    ccrg
    wcel
    #
    vm
    cB
    cR
    vp
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    cR
    cmgp
    cfv
    #
    vc
    cN
    vc
    cv
    #
    @3
    cfv
    #
    @9
    vm
    cv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    cK
    cD
    @0
    @11
    cB
    wcel
    #
    wa
    #
    cK
    vp
    cR
    @2
    @15
    mdetf.k
    @17
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    @0
    @18
    @16
    cR
    crngring
    #
    adantr
    #
    cR
    ringcmn
    syl
    @17
    cN
    cfn
    wcel
    #
    @2
    cfn
    wcel
    @17
    @21
    cR
    cvv
    wcel
    #
    @16
    @21
    @22
    wa
    @0
    cA
    cB
    cR
    cN
    @11
    mdetf.a
    mdetf.b
    matrcl
    adantl
    simpld
    #
    cN
    @2
    @1
    @1
    eqid
    #
    @2
    eqid
    #
    symgbasfi
    syl
    @17
    @15
    cK
    wcel
    #
    vp
    @2
    @17
    @3
    @2
    wcel
    #
    wa
    #
    @18
    @7
    cK
    wcel
    @13
    cK
    wcel
    @26
    @0
    @18
    @16
    @27
    @19
    ad2antrr
    @17
    @2
    cK
    @3
    @6
    @17
    @6
    @1
    @8
    cmhm
    co
    wcel
    #
    @2
    cK
    @6
    wf
    @17
    @18
    @21
    @29
    @20
    @23
    cN
    cR
    zrhpsgnmhm
    syl2anc
    @2
    cK
    @1
    @8
    @6
    @25
    cK
    cR
    @8
    @8
    eqid
    #
    mdetf.k
    mgpbas
    #
    mhmf
    syl
    ffvelrnda
    @28
    cK
    vc
    @8
    cN
    @12
    @31
    @0
    @8
    ccmn
    wcel
    @16
    @27
    cR
    @8
    @30
    crngmgp
    ad2antrr
    @17
    @21
    @27
    @23
    adantr
    @28
    @12
    cK
    wcel
    vc
    cN
    @28
    @9
    cN
    wcel
    #
    wa
    #
    @10
    @9
    cK
    cN
    cN
    @11
    @33
    @11
    cK
    cN
    cN
    cxp
    #
    cmap
    co
    wcel
    #
    @34
    cK
    @11
    wf
    @16
    @35
    @0
    @27
    @32
    cA
    cB
    cR
    cK
    @11
    cN
    mdetf.a
    mdetf.k
    mdetf.b
    matbas2i
    ad3antlr
    @11
    cK
    @34
    elmapi
    syl
    @28
    cN
    cN
    @9
    @3
    @27
    cN
    cN
    @3
    wf
    @17
    cN
    @2
    @3
    @1
    @24
    @25
    symgbasf
    adantl
    ffvelrnda
    @28
    @32
    simpr
    fovrnd
    ralrimiva
    gsummptcl
    cK
    cR
    @14
    @7
    @13
    mdetf.k
    @14
    eqid
    #
    ringcl
    syl3anc
    ralrimiva
    gsummptcl
    vc
    cA
    cB
    cD
    @2
    cR
    @5
    @14
    @8
    vm
    cN
    @4
    vp
    mdetf.d
    mdetf.a
    mdetf.b
    @25
    @4
    eqid
    @5
    eqid
    @36
    @30
    mdetfval
    fmptd
end
