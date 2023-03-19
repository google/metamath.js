include "cfv.mm"
include "cbrsiga.mm"
include "cv.mm"
include "cep.mm"
include "corvc.mm"
include "co.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "orvcelval.mm"
include "3eqtrd.mm"

theorem dstrvval
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cX: class X
  let va: setvar a
  assume dstrvprob.1: |- ( ph -> P e. Prob )
  assume dstrvprob.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume dstrvprob.3: |- ( ph -> D = ( a e. BrSiga |-> ( P ` ( X oRVC _E a ) ) ) )
  assume dstrvval.1: |- ( ph -> A e. BrSiga )

  disjoint A a
  disjoint P a
  disjoint X a
  assert |- ( ph -> ( D ` A ) = ( P ` ( `' X " A ) ) )

  proof
    wph
    cA
    cD
    cfv
    cA
    va
    cbrsiga
    cX
    va
    cv
    #
    cep
    corvc
    #
    co
    #
    cP
    cfv
    #
    cmpt
    #
    cfv
    #
    cX
    cA
    @1
    co
    #
    cP
    cfv
    #
    cX
    ccnv
    cA
    cima
    #
    cP
    cfv
    wph
    cA
    cD
    @4
    dstrvprob.3
    fveq1d
    wph
    cA
    cbrsiga
    wcel
    @5
    @7
    wceq
    dstrvval.1
    va
    cA
    @3
    @7
    cbrsiga
    @4
    @0
    cA
    wceq
    @2
    @6
    cP
    @0
    cA
    cX
    @1
    oveq2
    fveq2d
    @4
    eqid
    @6
    cP
    fvex
    fvmpt
    syl
    wph
    @6
    @8
    cP
    wph
    cA
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    dstrvval.1
    orvcelval
    fveq2d
    3eqtrd
end
