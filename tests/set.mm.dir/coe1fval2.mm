include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "cbs.mm"
include "ccom.mm"
include "wceq.mm"
include "ply1bascl.mm"
include "eqid.mm"
include "coe1fval3.mm"
include "syl.mm"

theorem coe1fval2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vn: setvar n
  assume coe1fval.a: |- A = ( coe1 ` F )
  assume coe1f.b: |- B = ( Base ` P )
  assume coe1f.p: |- P = ( Poly1 ` R )
  assume coe1fval2.g: |- G = ( y e. NN0 |-> ( 1o X. { y } ) )

  disjoint F y
  disjoint F f
  disjoint F n
  disjoint f n
  assert |- ( F e. B -> A = ( F o. G ) )

  proof
    cF
    cB
    wcel
    cF
    cR
    cps1
    cfv
    #
    cbs
    cfv
    #
    wcel
    cA
    cF
    cG
    ccom
    wceq
    cB
    cP
    cR
    cF
    coe1f.p
    coe1f.b
    ply1bascl
    vy
    cA
    @1
    @0
    cR
    cF
    cG
    coe1fval.a
    @1
    eqid
    @0
    eqid
    coe1fval2.g
    coe1fval3
    syl
end
