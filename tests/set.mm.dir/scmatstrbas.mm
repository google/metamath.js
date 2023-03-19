include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubrg.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "c0g.mm"
include "eqid.mm"
include "scmatsrng.mm"
include "subrgbas.mm"
include "eqcomd.mm"
include "syl.mm"

theorem scmatstrbas
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cN: class N
  assume scmatstrbas.a: |- A = ( N Mat R )
  assume scmatstrbas.c: |- C = ( N ScMat R )
  assume scmatstrbas.s: |- S = ( A |`s C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( Base ` S ) = C )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cC
    cA
    csubrg
    cfv
    wcel
    #
    cS
    cbs
    cfv
    #
    cC
    wceq
    cA
    cA
    cbs
    cfv
    #
    cR
    cC
    cR
    cbs
    cfv
    #
    cN
    cR
    c0g
    cfv
    #
    scmatstrbas.a
    @2
    eqid
    @3
    eqid
    @4
    eqid
    scmatstrbas.c
    scmatsrng
    @0
    cC
    @1
    cC
    cA
    cS
    scmatstrbas.s
    subrgbas
    eqcomd
    syl
end
