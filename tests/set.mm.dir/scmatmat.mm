include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "eqid.mm"
include "scmatel.mm"
include "simpl.mm"
include "syl6bi.mm"

theorem scmatmat
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  assume scmatmat.a: |- A = ( N Mat R )
  assume scmatmat.b: |- B = ( Base ` A )
  assume scmatmat.s: |- S = ( N ScMat R )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( M e. S -> M e. B ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    cM
    cS
    wcel
    cM
    cB
    wcel
    #
    cM
    vc
    cv
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    wceq
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    wa
    @0
    cA
    cB
    cR
    cS
    @2
    @1
    @3
    cM
    cN
    cV
    vc
    @3
    eqid
    scmatmat.a
    scmatmat.b
    @1
    eqid
    @2
    eqid
    scmatmat.s
    scmatel
    @0
    @4
    simpl
    syl6bi
end
