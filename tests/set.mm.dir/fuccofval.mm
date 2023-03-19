include "cco.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csb.mm"
include "ctp.mm"
include "eqidd.mm"
include "fucval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfunc.mm"
include "ovex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem fuccofval
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  assume fucval.q: |- Q = ( C FuncCat D )
  assume fucval.b: |- B = ( C Func D )
  assume fucval.n: |- N = ( C Nat D )
  assume fucval.a: |- A = ( Base ` C )
  assume fucval.o: |- .x. = ( comp ` D )
  assume fucval.c: |- ( ph -> C e. Cat )
  assume fucval.d: |- ( ph -> D e. Cat )
  assume fuccofval.x: |- .xb = ( comp ` Q )

  disjoint h v
  disjoint B h
  disjoint B v
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a v
  disjoint a x
  disjoint a ph
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b v
  disjoint b x
  disjoint b ph
  disjoint f g
  disjoint f h
  disjoint f v
  disjoint f x
  disjoint f ph
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint g ph
  disjoint h x
  disjoint h ph
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint C a
  disjoint C b
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C v
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D v
  disjoint D x
  disjoint h t
  disjoint h u
  disjoint t u
  disjoint t v
  disjoint B t
  disjoint u v
  disjoint B u
  disjoint N t
  disjoint N u
  disjoint a t
  disjoint a u
  disjoint b t
  disjoint b u
  disjoint f t
  disjoint f u
  disjoint g t
  disjoint g u
  disjoint t x
  disjoint ph t
  disjoint u x
  disjoint ph u
  disjoint .xb t
  disjoint .xb u
  disjoint C t
  disjoint C u
  disjoint D t
  disjoint D u
  assert |- ( ph -> .xb = ( v e. ( B X. B ) , h e. B |-> [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_ ( b e. ( g N h ) , a e. ( f N g ) |-> ( x e. A |-> ( ( b ` x ) ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. .x. ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) )

  proof
    wph
    cQ
    cco
    cfv
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    chom
    cfv
    cN
    cop
    #
    cnx
    cco
    cfv
    vv
    vh
    cB
    cB
    cxp
    #
    cB
    vf
    vv
    cv
    #
    c1st
    cfv
    vg
    @3
    c2nd
    cfv
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    cN
    co
    vf
    cv
    #
    @4
    cN
    co
    vx
    cA
    vx
    cv
    #
    vb
    cv
    cfv
    @7
    va
    cv
    cfv
    @7
    @6
    c1st
    cfv
    cfv
    @7
    @4
    c1st
    cfv
    cfv
    cop
    @7
    @5
    c1st
    cfv
    cfv
    c.x
    co
    co
    cmpt
    cmpt2
    csb
    csb
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    cco
    cfv
    #
    c.xb
    @9
    wph
    cQ
    @11
    cco
    wph
    vx
    vv
    cA
    cB
    cC
    cD
    cQ
    @9
    c.x
    vf
    vg
    vh
    cN
    va
    vb
    fucval.q
    fucval.b
    fucval.n
    fucval.a
    fucval.o
    fucval.c
    fucval.d
    wph
    @9
    eqidd
    fucval
    fveq2d
    fuccofval.x
    @9
    cvv
    wcel
    @9
    @12
    wceq
    vv
    vh
    @2
    cB
    @8
    cB
    cB
    cB
    cC
    cD
    cfunc
    co
    cvv
    fucval.b
    cC
    cD
    cfunc
    ovex
    eqeltri
    #
    @13
    xpex
    @13
    mpt2ex
    @9
    @11
    cco
    cvv
    c1
    c1
    c5
    cdc
    cop
    @9
    cB
    cN
    catstr
    ccoid
    @0
    @1
    @10
    snsstp3
    strfv
    ax-mp
    3eqtr4g
end
