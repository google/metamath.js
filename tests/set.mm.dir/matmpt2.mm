include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapfn.mm"
include "syl.mm"
include "fnov.mm"
include "sylib.mm"

theorem matmpt2
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  assume matmpt2.a: |- A = ( N Mat R )
  assume matmpt2.n: |- B = ( Base ` A )

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B i
  disjoint B j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  assert |- ( M e. B -> M = ( i e. N , j e. N |-> ( i M j ) ) )

  proof
    cM
    cB
    wcel
    #
    cM
    cN
    cN
    cxp
    #
    wfn
    #
    cM
    vi
    vj
    cN
    cN
    vi
    cv
    vj
    cv
    cM
    co
    cmpt2
    wceq
    @0
    cM
    cR
    cbs
    cfv
    #
    @1
    cmap
    co
    wcel
    @2
    cA
    cB
    cR
    @3
    cM
    cN
    matmpt2.a
    @3
    eqid
    matmpt2.n
    matbas2i
    cM
    @3
    @1
    elmapfn
    syl
    vi
    vj
    cN
    cN
    cM
    fnov
    sylib
end
