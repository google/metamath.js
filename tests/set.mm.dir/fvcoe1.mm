include "wcel.mm"
include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsnconst.mm"
include "adantl.mm"
include "fveq2d.mm"
include "wf.mm"
include "elmapi.mm"
include "0lt1o.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "coe1fv.mm"
include "sylan2.mm"
include "eqtr4d.mm"

theorem fvcoe1
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let cN: class N
  let vn: setvar n
  let vf: setvar f
  assume coe1fval.a: |- A = ( coe1 ` F )


  assert |- ( ( F e. V /\ X e. ( NN0 ^m 1o ) ) -> ( F ` X ) = ( A ` ( X ` (/) ) ) )

  proof
    cF
    cV
    wcel
    #
    cX
    cn0
    c1o
    cmap
    co
    wcel
    #
    wa
    #
    cX
    cF
    cfv
    c1o
    c0
    cX
    cfv
    #
    csn
    cxp
    #
    cF
    cfv
    #
    @3
    cA
    cfv
    #
    @2
    cX
    @4
    cF
    @1
    cX
    @4
    wceq
    @0
    cn0
    c1o
    cX
    c0
    df1o2
    nn0ex
    0ex
    mapsnconst
    adantl
    fveq2d
    @1
    @0
    @3
    cn0
    wcel
    #
    @6
    @5
    wceq
    @1
    c1o
    cn0
    cX
    wf
    c0
    c1o
    wcel
    @7
    cX
    cn0
    c1o
    elmapi
    0lt1o
    c1o
    cn0
    c0
    cX
    ffvelrn
    sylancl
    cA
    cF
    @3
    cV
    coe1fval.a
    coe1fv
    sylan2
    eqtr4d
end
