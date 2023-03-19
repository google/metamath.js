include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapfn.mm"
include "syl.mm"
include "eqfnov2.mm"
include "syl2an.mm"

theorem eqmat
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let cX: class X
  let cY: class Y
  assume eqmat.a: |- A = ( N Mat R )
  assume eqmat.b: |- B = ( Base ` A )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
  assert |- ( ( X e. B /\ Y e. B ) -> ( X = Y <-> A. i e. N A. j e. N ( i X j ) = ( i Y j ) ) )

  proof
    cX
    cB
    wcel
    #
    cX
    cN
    cN
    cxp
    #
    wfn
    #
    cY
    @1
    wfn
    #
    cX
    cY
    wceq
    vi
    cv
    #
    vj
    cv
    #
    cX
    co
    @4
    @5
    cY
    co
    wceq
    vj
    cN
    wral
    vi
    cN
    wral
    wb
    cY
    cB
    wcel
    #
    @0
    cX
    cR
    cbs
    cfv
    #
    @1
    cmap
    co
    #
    wcel
    @2
    cA
    cB
    cR
    @7
    cX
    cN
    eqmat.a
    @7
    eqid
    #
    eqmat.b
    matbas2i
    cX
    @7
    @1
    elmapfn
    syl
    @6
    cY
    @8
    wcel
    @3
    cA
    cB
    cR
    @7
    cY
    cN
    eqmat.a
    @9
    eqmat.b
    matbas2i
    cY
    @7
    @1
    elmapfn
    syl
    vi
    vj
    cN
    cN
    cX
    cY
    eqfnov2
    syl2an
end
