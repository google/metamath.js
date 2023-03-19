include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "cmpt.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "cnbgr.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "nbusgrf1o0.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "sylc.mm"

theorem nbusgrf1o1
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let cM: class M
  let vn: setvar n
  assume nbusgrf1o1.v: |- V = ( Vtx ` G )
  assume nbusgrf1o1.e: |- E = ( Edg ` G )
  assume nbusgrf1o1.n: |- N = ( G NeighbVtx U )
  assume nbusgrf1o1.i: |- I = { e e. E | U e. e }

  disjoint E e
  disjoint U e
  disjoint G e
  disjoint I e
  disjoint N e
  disjoint V e
  disjoint I f
  disjoint N f
  disjoint U f
  disjoint E i
  disjoint e i
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint U i
  disjoint V i
  disjoint E n
  disjoint G n
  disjoint e n
  disjoint I n
  disjoint N n
  disjoint U n
  disjoint V n
  disjoint f n
  assert |- ( ( G e. USGraph /\ U e. V ) -> E. f f : N -1-1-onto-> I )

  proof
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    #
    vn
    cN
    cU
    vn
    cv
    cpr
    #
    cmpt
    #
    cvv
    wcel
    #
    cN
    cI
    @2
    wf1o
    #
    cN
    cI
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    cN
    cvv
    wcel
    @3
    @0
    cN
    cG
    cU
    cnbgr
    co
    cvv
    nbusgrf1o1.n
    cG
    cU
    cnbgr
    ovex
    eqeltri
    vn
    cN
    @1
    cvv
    mptexg
    mp1i
    cU
    ve
    vn
    cE
    @2
    cG
    cI
    cN
    cV
    nbusgrf1o1.v
    nbusgrf1o1.e
    nbusgrf1o1.n
    nbusgrf1o1.i
    @2
    eqid
    nbusgrf1o0
    @6
    @4
    vf
    @2
    cvv
    cN
    cI
    @5
    @2
    f1oeq1
    spcegv
    sylc
end
