include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "konigthlem.mm"

theorem konigth
  let cA: class A
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cM: class M
  let cN: class N
  let va: setvar a
  let ve: setvar e
  let vf: setvar f
  let vj: setvar j
  let vb: setvar b
  assume konigth.1: |- A e. _V
  assume konigth.2: |- S = U_ i e. A ( M ` i )
  assume konigth.3: |- P = X_ i e. A ( N ` i )

  disjoint A i
  disjoint A a
  disjoint A e
  disjoint A f
  disjoint a e
  disjoint a f
  disjoint a i
  disjoint e f
  disjoint e i
  disjoint f i
  disjoint A j
  disjoint a j
  disjoint e j
  disjoint i j
  disjoint M a
  disjoint M b
  disjoint M e
  disjoint M f
  disjoint a b
  disjoint b e
  disjoint b f
  disjoint N a
  disjoint N e
  disjoint N f
  disjoint P a
  disjoint P e
  disjoint P f
  disjoint S a
  disjoint S e
  disjoint S f
  disjoint b i
  assert |- ( A. i e. A ( M ` i ) ~< ( N ` i ) -> S ~< P )

  proof
    cA
    vi
    cA
    vb
    vi
    cv
    #
    cM
    cfv
    #
    @0
    vb
    cv
    #
    vf
    cv
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    cP
    cS
    ve
    vf
    vi
    vj
    cA
    vj
    cv
    #
    ve
    cv
    #
    cfv
    #
    cmpt
    cM
    cN
    va
    konigth.1
    konigth.2
    konigth.3
    vi
    cA
    @6
    va
    @1
    @0
    va
    cv
    #
    @3
    cfv
    #
    cfv
    #
    cmpt
    vb
    va
    @1
    @5
    @12
    vb
    va
    weq
    @0
    @4
    @11
    @2
    @10
    @3
    fveq2
    fveq1d
    cbvmptv
    mpteq2i
    vj
    vi
    cA
    @9
    @0
    @8
    cfv
    @7
    @0
    @8
    fveq2
    cbvmptv
    konigthlem
end
