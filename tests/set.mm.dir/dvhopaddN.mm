include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cxp.mm"
include "wceq.mm"
include "opelxpi.mm"
include "dvhvaddval.mm"
include "syl2an.mm"
include "op1stg.mm"
include "adantr.mm"
include "adantl.mm"
include "coeq12d.mm"
include "op2ndg.mm"
include "oveqan12d.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem dvhopaddN
  let cA: class A
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  assume dvhopadd.a: |- A = ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( ( 2nd ` f ) P ( 2nd ` g ) ) >. )

  disjoint f g
  disjoint E f
  disjoint E g
  disjoint P f
  disjoint P g
  disjoint T f
  disjoint T g
  assert |- ( ( ( F e. T /\ U e. E ) /\ ( G e. T /\ V e. E ) ) -> ( <. F , U >. A <. G , V >. ) = <. ( F o. G ) , ( U P V ) >. )

  proof
    cF
    cT
    wcel
    cU
    cE
    wcel
    wa
    #
    cG
    cT
    wcel
    cV
    cE
    wcel
    wa
    #
    wa
    #
    cF
    cU
    cop
    #
    cG
    cV
    cop
    #
    cA
    co
    #
    @3
    c1st
    cfv
    #
    @4
    c1st
    cfv
    #
    ccom
    #
    @3
    c2nd
    cfv
    #
    @4
    c2nd
    cfv
    #
    cP
    co
    #
    cop
    #
    cF
    cG
    ccom
    #
    cU
    cV
    cP
    co
    #
    cop
    @0
    @3
    cT
    cE
    cxp
    #
    wcel
    @4
    @15
    wcel
    @5
    @12
    wceq
    @1
    cF
    cU
    cT
    cE
    opelxpi
    cG
    cV
    cT
    cE
    opelxpi
    cA
    cP
    cT
    vf
    vg
    cE
    @3
    @4
    dvhopadd.a
    dvhvaddval
    syl2an
    @2
    @8
    @13
    @11
    @14
    @2
    @6
    cF
    @7
    cG
    @0
    @6
    cF
    wceq
    @1
    cF
    cU
    cT
    cE
    op1stg
    adantr
    @1
    @7
    cG
    wceq
    @0
    cG
    cV
    cT
    cE
    op1stg
    adantl
    coeq12d
    @0
    @1
    @9
    cU
    @10
    cV
    cP
    cF
    cU
    cT
    cE
    op2ndg
    cG
    cV
    cT
    cE
    op2ndg
    oveqan12d
    opeq12d
    eqtrd
end
