include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "crdg.mm"
include "cima.mm"
include "seqomlem0.mm"
include "seqomlem4.mm"
include "cseqom.mm"
include "df-seqom.mm"
include "eqtri.mm"
include "fveq1i.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"

theorem seqomsuc
  let cA: class A
  let cF: class F
  let cG: class G
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume seqom.a: |- G = seqom ( F , I )


  assert |- ( A e. _om -> ( G ` suc A ) = ( A F ( G ` A ) ) )

  proof
    cA
    com
    wcel
    cA
    csuc
    #
    va
    vb
    com
    cvv
    va
    cv
    #
    csuc
    @1
    vb
    cv
    cF
    co
    cop
    cmpt2
    c0
    cI
    cid
    cfv
    cop
    crdg
    #
    com
    cima
    #
    cfv
    cA
    cA
    @3
    cfv
    #
    cF
    co
    @0
    cG
    cfv
    cA
    cA
    cG
    cfv
    #
    cF
    co
    vd
    cA
    @2
    vc
    cF
    cI
    cF
    cI
    va
    vb
    vc
    vd
    seqomlem0
    seqomlem4
    @0
    cG
    @3
    cG
    cF
    cI
    cseqom
    @3
    seqom.a
    vb
    va
    cF
    cI
    df-seqom
    eqtri
    #
    fveq1i
    @5
    @4
    cA
    cF
    cA
    cG
    @3
    @6
    fveq1i
    oveq2i
    3eqtr4g
end
