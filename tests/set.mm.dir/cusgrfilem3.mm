include "wcel.mm"
include "cfn.mm"
include "csn.mm"
include "cdif.mm"
include "diffi.mm"
include "wn.mm"
include "wa.mm"
include "simpr.mm"
include "snfi.mm"
include "difinf.mm"
include "sylancl.mm"
include "ex.mm"
include "con4d.mm"
include "impbid2.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cvv.mm"
include "cpr.mm"
include "cmpt.mm"
include "cvtx.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "ax-mp.mm"
include "mptexg.mm"
include "mp1i.mm"
include "syl5eqel.mm"
include "cusgrfilem2.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "bren.mm"
include "sylibr.mm"
include "enfi.mm"
include "syl.mm"
include "bitrd.mm"

theorem cusgrfilem3
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vv: setvar v
  let vf: setvar f
  assume cusgrfi.v: |- V = ( Vtx ` G )
  assume cusgrfi.p: |- P = { x e. ~P V | E. a e. V ( a =/= N /\ x = { a , N } ) }
  assume cusgrfi.f: |- F = ( x e. ( V \ { N } ) |-> { x , N } )

  disjoint G x
  disjoint N a
  disjoint N x
  disjoint a x
  disjoint V a
  disjoint V x
  disjoint P x
  disjoint F e
  disjoint N e
  disjoint a e
  disjoint e x
  disjoint N v
  disjoint a v
  disjoint v x
  disjoint P e
  disjoint V e
  disjoint V v
  disjoint F f
  disjoint N f
  disjoint P f
  disjoint V f
  assert |- ( N e. V -> ( V e. Fin <-> P e. Fin ) )

  proof
    cN
    cV
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    cN
    csn
    #
    cdif
    #
    cfn
    wcel
    #
    cP
    cfn
    wcel
    #
    @0
    @1
    @4
    cV
    @2
    diffi
    @0
    @1
    @4
    @0
    @1
    wn
    #
    @4
    wn
    #
    @0
    @6
    wa
    @6
    @2
    cfn
    wcel
    @7
    @0
    @6
    simpr
    cN
    snfi
    cV
    @2
    difinf
    sylancl
    ex
    con4d
    impbid2
    @0
    @3
    cP
    cen
    wbr
    #
    @4
    @5
    wb
    @0
    @3
    cP
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @8
    @0
    cF
    cvv
    wcel
    @3
    cP
    cF
    wf1o
    #
    @11
    @0
    cF
    vx
    @3
    vx
    cv
    cN
    cpr
    #
    cmpt
    #
    cvv
    cusgrfi.f
    @3
    cvv
    wcel
    #
    @14
    cvv
    wcel
    @0
    cV
    cvv
    wcel
    @15
    cV
    cG
    cvtx
    cfv
    cvv
    cusgrfi.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    @2
    cvv
    difexg
    ax-mp
    vx
    @3
    @13
    cvv
    mptexg
    mp1i
    syl5eqel
    vx
    cP
    cF
    cG
    cN
    cV
    va
    cusgrfi.v
    cusgrfi.p
    cusgrfi.f
    cusgrfilem2
    @10
    @12
    vf
    cF
    cvv
    @3
    cP
    @9
    cF
    f1oeq1
    spcegv
    sylc
    @3
    cP
    vf
    bren
    sylibr
    @3
    cP
    enfi
    syl
    bitrd
end
