include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cco1.mm"
include "con0.mm"
include "cmpl.mm"
include "co.mm"
include "eqid.mm"
include "deg1fval.mm"
include "1on.mm"
include "a1i.mm"
include "simpl.mm"
include "cps1.mm"
include "ply1bas.mm"
include "ply1ascl.mm"
include "simpr.mm"
include "mdegle0.mm"
include "cn0.mm"
include "0nn0.mm"
include "coe1fv.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "bitr4d.mm"

theorem deg1le0
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  assume deg1le0.d: |- D = ( deg1 ` R )
  assume deg1le0.p: |- P = ( Poly1 ` R )
  assume deg1le0.b: |- B = ( Base ` P )
  assume deg1le0.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. B ) -> ( ( D ` F ) <_ 0 <-> F = ( A ` ( ( coe1 ` F ) ` 0 ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    wa
    #
    cF
    cD
    cfv
    cc0
    cle
    wbr
    cF
    c1o
    cc0
    csn
    cxp
    cF
    cfv
    #
    cA
    cfv
    #
    wceq
    cF
    cc0
    cF
    cco1
    cfv
    #
    cfv
    #
    cA
    cfv
    #
    wceq
    @2
    cA
    cB
    cD
    cR
    cF
    c1o
    con0
    c1o
    cR
    cmpl
    co
    #
    @8
    eqid
    cD
    cR
    deg1le0.d
    deg1fval
    c1o
    con0
    wcel
    @2
    1on
    a1i
    @0
    @1
    simpl
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1le0.p
    @9
    eqid
    deg1le0.b
    ply1bas
    cA
    cP
    cR
    deg1le0.p
    deg1le0.a
    ply1ascl
    @0
    @1
    simpr
    #
    mdegle0
    @2
    @7
    @4
    cF
    @2
    @6
    @3
    cA
    @2
    @1
    cc0
    cn0
    wcel
    @6
    @3
    wceq
    @10
    0nn0
    @5
    cF
    cc0
    cB
    @5
    eqid
    coe1fv
    sylancl
    fveq2d
    eqeq2d
    bitr4d
end
