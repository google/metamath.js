include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cid.mm"
include "com.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cima.mm"
include "cseqom.mm"
include "df-seqom.mm"
include "eqtri.mm"
include "fveq1i.mm"
include "seqomlem0.mm"
include "seqomlem3.mm"
include "fvi.mm"
include "syl5eq.mm"

theorem seqom0g
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  assume seqom.a: |- G = seqom ( F , I )


  assert |- ( I e. V -> ( G ` (/) ) = I )

  proof
    cI
    cV
    wcel
    c0
    cG
    cfv
    #
    cI
    cid
    cfv
    #
    cI
    @0
    c0
    va
    vb
    com
    cvv
    va
    cv
    #
    csuc
    @2
    vb
    cv
    cF
    co
    cop
    cmpt2
    c0
    @1
    cop
    crdg
    #
    com
    cima
    #
    cfv
    @1
    c0
    cG
    @4
    cG
    cF
    cI
    cseqom
    @4
    seqom.a
    vb
    va
    cF
    cI
    df-seqom
    eqtri
    fveq1i
    vd
    @3
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
    seqomlem3
    eqtri
    cI
    cV
    fvi
    syl5eq
end
