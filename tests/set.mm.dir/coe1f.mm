include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "cbs.mm"
include "cn0.mm"
include "wf.mm"
include "ply1bascl.mm"
include "eqid.mm"
include "coe1f2.mm"
include "syl.mm"

theorem coe1f
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  let vf: setvar f
  let vn: setvar n
  assume coe1fval.a: |- A = ( coe1 ` F )
  assume coe1f.b: |- B = ( Base ` P )
  assume coe1f.p: |- P = ( Poly1 ` R )
  assume coe1f.k: |- K = ( Base ` R )


  assert |- ( F e. B -> A : NN0 --> K )

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
    cn0
    cK
    cA
    wf
    cB
    cP
    cR
    cF
    coe1f.p
    coe1f.b
    ply1bascl
    cA
    @1
    @0
    cR
    cF
    cK
    coe1fval.a
    @1
    eqid
    @0
    eqid
    coe1f.k
    coe1f2
    syl
end
