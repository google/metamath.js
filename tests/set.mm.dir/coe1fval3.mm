include "wcel.mm"
include "cn0.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "coe1fval.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wf.mm"
include "wceq.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "psr1basf.mm"
include "ssv.mm"
include "fss.mm"
include "sylancl.mm"
include "wa.mm"
include "fconst6g.mm"
include "adantl.mm"
include "nn0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "elmap.mm"
include "sylibr.mm"
include "a1i.mm"
include "id.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem coe1fval3
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vf: setvar f
  let vn: setvar n
  assume coe1fval.a: |- A = ( coe1 ` F )
  assume coe1f2.b: |- B = ( Base ` P )
  assume coe1f2.p: |- P = ( PwSer1 ` R )
  assume coe1fval3.g: |- G = ( y e. NN0 |-> ( 1o X. { y } ) )

  disjoint F y
  disjoint F x
  disjoint x y
  disjoint F f
  disjoint F n
  disjoint f n
  assert |- ( F e. B -> A = ( F o. G ) )

  proof
    cF
    cB
    wcel
    #
    cA
    vy
    cn0
    c1o
    vy
    cv
    #
    csn
    cxp
    #
    cF
    cfv
    #
    cmpt
    #
    cF
    cG
    ccom
    #
    cA
    vy
    cF
    cB
    coe1fval.a
    coe1fval
    @0
    cn0
    c1o
    cmap
    co
    #
    cvv
    cF
    wf
    #
    @5
    @4
    wceq
    @0
    @6
    cR
    cbs
    cfv
    #
    cF
    wf
    @8
    cvv
    wss
    @7
    cB
    cP
    cR
    cF
    @8
    coe1f2.p
    coe1f2.b
    @8
    eqid
    psr1basf
    @8
    ssv
    @6
    @8
    cvv
    cF
    fss
    sylancl
    @7
    vy
    vx
    cn0
    @6
    @2
    vx
    cv
    #
    cF
    cfv
    @3
    cG
    cF
    @7
    @1
    cn0
    wcel
    #
    wa
    c1o
    cn0
    @2
    wf
    #
    @2
    @6
    wcel
    @10
    @11
    @7
    c1o
    @1
    cn0
    fconst6g
    adantl
    cn0
    c1o
    @2
    nn0ex
    c1o
    con0
    1on
    elexi
    elmap
    sylibr
    cG
    vy
    cn0
    @2
    cmpt
    wceq
    @7
    coe1fval3.g
    a1i
    @7
    vx
    @6
    cvv
    cF
    @7
    id
    feqmptd
    @9
    @2
    cF
    fveq2
    fmptco
    syl
    eqtr4d
end
