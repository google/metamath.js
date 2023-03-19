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
include "simpld.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq2d.mm"
include "chom.mm"
include "ccat.mm"
include "funcrcl.mm"
include "simprd.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "nat1st2nd.mm"
include "simpr.mm"
include "natcl.mm"
include "catrid.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fucidcl.mm"
include "fucco.mm"
include "wfn.mm"
include "natfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4d.mm"

theorem fucrid
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


  assert |- ( ph -> ( R ( <. F , F >. .xb G ) ( .1. o. ( 1st ` F ) ) ) = R )

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
    cR
    cfv
    #
    @1
    c.1
    cF
    c1st
    cfv
    #
    ccom
    #
    cfv
    #
    @1
    @3
    cfv
    #
    @6
    cop
    @1
    cG
    c1st
    cfv
    #
    cfv
    #
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
    @2
    cmpt
    #
    cR
    @4
    cF
    cF
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
    @2
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @11
    @2
    @6
    c.1
    cfv
    #
    @10
    co
    @2
    @14
    @5
    @15
    @2
    @10
    wph
    @0
    cD
    cbs
    cfv
    #
    @3
    wf
    @13
    @5
    @15
    wceq
    wph
    @0
    @16
    cC
    cD
    @3
    cF
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
    cF
    @20
    wcel
    #
    @3
    @17
    @20
    wbr
    cC
    cD
    relfunc
    #
    wph
    @22
    cG
    @20
    wcel
    #
    wph
    cR
    cF
    cG
    cN
    co
    wcel
    @22
    @24
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
    simpld
    #
    cF
    @20
    1st2ndbr
    sylancr
    funcf1
    #
    @0
    @16
    @1
    c.1
    @3
    fvco3
    sylan
    oveq2d
    @14
    @16
    cD
    @9
    c.1
    @2
    cD
    chom
    cfv
    #
    @6
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
    @22
    @31
    @30
    wa
    @26
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
    @3
    @27
    ffvelrnda
    @9
    eqid
    #
    wph
    @0
    @16
    @1
    @7
    wph
    @0
    @16
    cC
    cD
    @7
    cG
    c2nd
    cfv
    #
    @18
    @19
    wph
    @21
    @24
    @7
    @33
    @20
    wbr
    @23
    wph
    @22
    @24
    @25
    simprd
    cG
    @20
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @14
    cR
    @0
    cC
    cD
    @3
    @17
    @28
    @7
    @33
    cN
    @1
    fuclid.n
    wph
    cR
    @3
    @17
    cop
    @7
    @33
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
    catrid
    eqtrd
    mpteq2dva
    wph
    vx
    @0
    cC
    cD
    cQ
    @4
    cR
    c.xb
    @9
    cF
    cF
    cG
    cN
    fuclid.q
    fuclid.n
    @18
    @32
    fuclid.x
    wph
    cC
    cD
    cQ
    c.1
    cF
    cN
    fuclid.q
    fuclid.n
    fuclid.1
    @26
    fucidcl
    fuclid.r
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
    @3
    @17
    @7
    @33
    cN
    fuclid.n
    @34
    @18
    natfn
    vx
    @0
    cR
    dffn5
    sylib
    3eqtr4d
end
