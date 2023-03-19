include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cfn.mm"
include "cvv.mm"
include "wa.mm"
include "n0i.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "cmat.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cnx.mm"
include "cmulr.mm"
include "cotp.mm"
include "cmmul.mm"
include "cop.mm"
include "csts.mm"
include "df-mat.mm"
include "mpt2ndm0.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "nsyl2.mm"

theorem matrcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume matrcl.a: |- A = ( N Mat R )
  assume matrcl.b: |- B = ( Base ` A )


  assert |- ( X e. B -> ( N e. Fin /\ R e. _V ) )

  proof
    cX
    cB
    wcel
    cB
    c0
    wceq
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    #
    cB
    cX
    n0i
    @0
    wn
    #
    cA
    cbs
    cfv
    c0
    cbs
    cfv
    cB
    c0
    @1
    cA
    c0
    cbs
    @1
    cA
    cN
    cR
    cmat
    co
    c0
    matrcl.a
    va
    vb
    vb
    cv
    #
    va
    cv
    #
    @3
    cxp
    cfrlm
    co
    cnx
    cmulr
    cfv
    @2
    @3
    @3
    @3
    cotp
    cmmul
    co
    cop
    csts
    co
    cmat
    cN
    cR
    cfn
    cvv
    va
    vb
    df-mat
    mpt2ndm0
    syl5eq
    fveq2d
    matrcl.b
    base0
    3eqtr4g
    nsyl2
end
