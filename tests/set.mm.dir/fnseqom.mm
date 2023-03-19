include "com.mm"
include "wfn.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "crdg.mm"
include "cima.mm"
include "seqomlem0.mm"
include "seqomlem2.mm"
include "cseqom.mm"
include "df-seqom.mm"
include "eqtri.mm"
include "fneq1i.mm"
include "mpbir.mm"

theorem fnseqom
  let cF: class F
  let cG: class G
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  assume seqom.a: |- G = seqom ( F , I )


  assert |- G Fn _om

  proof
    cG
    com
    wfn
    va
    vb
    com
    cvv
    va
    cv
    #
    csuc
    @0
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
    com
    wfn
    vd
    @1
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
    seqomlem2
    com
    cG
    @2
    cG
    cF
    cI
    cseqom
    @2
    seqom.a
    vb
    va
    cF
    cI
    df-seqom
    eqtri
    fneq1i
    mpbir
end
