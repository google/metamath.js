include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "c2nd.mm"
include "eqid.mm"
include "cfunc.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "natrcl.mm"
include "syl.mm"
include "simprd.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq1d.mm"
include "chom.mm"
include "ccat.mm"
include "simpld.mm"
include "funcrcl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "nat1st2nd.mm"
include "simpr.mm"
include "natcl.mm"
include "catlid.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fucidcl.mm"
include "fucco.mm"
include "wfn.mm"
include "natfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4d.mm"

theorem fuclid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let c.xb: class .xb
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cN: class N
  let vx: setvar x
  assume fuclid.q: |- Q = ( C FuncCat D )
  assume fuclid.n: |- N = ( C Nat D )
  assume fuclid.x: |- .xb = ( comp ` Q )
  assume fuclid.1: |- .1. = ( Id ` D )
  assume fuclid.r: |- ( ph -> R e. ( F N G ) )


  assert |- ( ph -> ( ( .1. o. ( 1st ` G ) ) ( <. F , G >. .xb G ) R ) = R )

  proof
    wph
    vx
    cC
    cbs
    cfv
    #
    vx
    cv
    #
    c.1
    cG
    c1st
    cfv
    #
    ccom
    #
    cfv
    #
    @1
    cR
    cfv
    #
    @1
    cF
    c1st
    cfv
    #
    cfv
    #
    @1
    @2
    cfv
    #
    cop
    @8
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    vx
    @0
    @5
    cmpt
    #
    @3
    cR
    cF
    cG
    cop
    cG
    c.xb
    co
    co
    cR
    wph
    vx
    @0
    @11
    @5
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @11
    @8
    c.1
    cfv
    #
    @5
    @10
    co
    @5
    @14
    @4
    @15
    @5
    @10
    wph
    @0
    cD
    cbs
    cfv
    #
    @2
    wf
    @13
    @4
    @15
    wceq
    wph
    @0
    @16
    cC
    cD
    @2
    cG
    c2nd
    cfv
    #
    @0
    eqid
    #
    @16
    eqid
    #
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    #
    cG
    @20
    wcel
    #
    @2
    @17
    @20
    wbr
    cC
    cD
    relfunc
    #
    wph
    cF
    @20
    wcel
    #
    @22
    wph
    cR
    cF
    cG
    cN
    co
    wcel
    @24
    @22
    wa
    fuclid.r
    cR
    cC
    cD
    cF
    cG
    cN
    fuclid.n
    natrcl
    syl
    #
    simprd
    #
    cG
    @20
    1st2ndbr
    sylancr
    funcf1
    #
    @0
    @16
    @1
    c.1
    @2
    fvco3
    sylan
    oveq1d
    @14
    @16
    cD
    @9
    c.1
    @5
    cD
    chom
    cfv
    #
    @7
    @8
    @19
    @28
    eqid
    #
    fuclid.1
    wph
    cD
    ccat
    wcel
    #
    @13
    wph
    cC
    ccat
    wcel
    #
    @30
    wph
    @24
    @31
    @30
    wa
    wph
    @24
    @22
    @25
    simpld
    #
    cC
    cD
    cF
    funcrcl
    syl
    simprd
    adantr
    wph
    @0
    @16
    @1
    @6
    wph
    @0
    @16
    cC
    cD
    @6
    cF
    c2nd
    cfv
    #
    @18
    @19
    wph
    @21
    @24
    @6
    @33
    @20
    wbr
    @23
    @32
    cF
    @20
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @9
    eqid
    #
    wph
    @0
    @16
    @1
    @2
    @27
    ffvelrnda
    @14
    cR
    @0
    cC
    cD
    @6
    @33
    @28
    @2
    @17
    cN
    @1
    fuclid.n
    wph
    cR
    @6
    @33
    cop
    @2
    @17
    cop
    cN
    co
    wcel
    @13
    wph
    cR
    cC
    cD
    cF
    cG
    cN
    fuclid.n
    fuclid.r
    nat1st2nd
    #
    adantr
    @18
    @29
    wph
    @13
    simpr
    natcl
    catlid
    eqtrd
    mpteq2dva
    wph
    vx
    @0
    cC
    cD
    cQ
    cR
    @3
    c.xb
    @9
    cF
    cG
    cG
    cN
    fuclid.q
    fuclid.n
    @18
    @34
    fuclid.x
    fuclid.r
    wph
    cC
    cD
    cQ
    c.1
    cG
    cN
    fuclid.q
    fuclid.n
    fuclid.1
    @26
    fucidcl
    fucco
    wph
    cR
    @0
    wfn
    cR
    @12
    wceq
    wph
    cR
    @0
    cC
    cD
    @6
    @33
    @2
    @17
    cN
    fuclid.n
    @35
    @18
    natfn
    vx
    @0
    cR
    dffn5
    sylib
    3eqtr4d
end
