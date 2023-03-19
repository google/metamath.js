include "wdisj.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvdisjf.mm"
include "csbeq1.mm"
include "disjor.mm"
include "bitri.mm"

theorem disjorsf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  assume disjorsf.1: |- F/_ x A

  disjoint i j
  disjoint i x
  disjoint j x
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  assert |- ( Disj_ x e. A B <-> A. i e. A A. j e. A ( i = j \/ ( [_ i / x ]_ B i^i [_ j / x ]_ B ) = (/) ) )

  proof
    vx
    cA
    cB
    wdisj
    vi
    cA
    vx
    vi
    cv
    #
    cB
    csb
    #
    wdisj
    @0
    vj
    cv
    #
    wceq
    @1
    vx
    @2
    cB
    csb
    #
    cin
    c0
    wceq
    wo
    vj
    cA
    wral
    vi
    cA
    wral
    vx
    vi
    cA
    cB
    @1
    disjorsf.1
    vi
    cB
    nfcv
    vx
    @0
    cB
    nfcsb1v
    vx
    @0
    cB
    csbeq1a
    cbvdisjf
    cA
    @1
    @3
    vi
    vj
    vx
    @0
    @2
    cB
    csbeq1
    disjor
    bitri
end
