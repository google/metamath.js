include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cxp.mm"
include "wceq.mm"
include "opelxpi.mm"
include "dvhvscaval.mm"
include "sylan2.mm"
include "op1stg.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "coeq2d.mm"
include "opeq12d.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem dvhopspN
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let vs: setvar s
  assume dvhopsp.s: |- S = ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. )

  disjoint f s
  disjoint E f
  disjoint E s
  disjoint T f
  disjoint T s
  assert |- ( ( R e. E /\ ( F e. T /\ U e. E ) ) -> ( R S <. F , U >. ) = <. ( R ` F ) , ( R o. U ) >. )

  proof
    cR
    cE
    wcel
    #
    cF
    cT
    wcel
    cU
    cE
    wcel
    wa
    #
    wa
    cR
    cF
    cU
    cop
    #
    cS
    co
    #
    @2
    c1st
    cfv
    #
    cR
    cfv
    #
    cR
    @2
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    cF
    cR
    cfv
    #
    cR
    cU
    ccom
    #
    cop
    #
    @1
    @0
    @2
    cT
    cE
    cxp
    wcel
    @3
    @8
    wceq
    cF
    cU
    cT
    cE
    opelxpi
    cT
    cS
    cR
    vf
    cE
    @2
    vs
    dvhopsp.s
    dvhvscaval
    sylan2
    @1
    @8
    @11
    wceq
    @0
    @1
    @5
    @9
    @7
    @10
    @1
    @4
    cF
    cR
    cF
    cU
    cT
    cE
    op1stg
    fveq2d
    @1
    @6
    cU
    cR
    cF
    cU
    cT
    cE
    op2ndg
    coeq2d
    opeq12d
    adantl
    eqtrd
end
