include "ctop.mm"
include "wcel.mm"
include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "dssmapntrcls.mm"
include "eqcomd.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wi.mm"
include "topopn.mm"
include "dssmapf1od.mm"
include "clselmap.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "mpd.mm"
include "dssmapnvod.mm"
include "fveq1d.mm"
include "eqtr3d.mm"

theorem dssmapclsntr
  let cD: class D
  let vf: setvar f
  let cI: class I
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  assume dssmapclsntr.x: |- X = U. J
  assume dssmapclsntr.k: |- K = ( cls ` J )
  assume dssmapclsntr.i: |- I = ( int ` J )
  assume dssmapclsntr.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapclsntr.d: |- D = ( O ` X )

  disjoint J b
  disjoint J f
  disjoint J s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint K f
  disjoint K s
  disjoint X b
  disjoint X f
  disjoint X s
  assert |- ( J e. Top -> K = ( D ` I ) )

  proof
    cJ
    ctop
    wcel
    #
    cI
    cD
    ccnv
    #
    cfv
    #
    cK
    cI
    cD
    cfv
    @0
    cK
    cD
    cfv
    #
    cI
    wceq
    #
    @2
    cK
    wceq
    #
    @0
    cI
    @3
    cD
    vf
    cI
    cJ
    cK
    cO
    cX
    vs
    vb
    dssmapclsntr.x
    dssmapclsntr.k
    dssmapclsntr.i
    dssmapclsntr.o
    dssmapclsntr.d
    dssmapntrcls
    eqcomd
    @0
    cX
    cpw
    #
    @6
    cmap
    co
    #
    @7
    cD
    wf1o
    cK
    @7
    wcel
    @4
    @5
    wi
    @0
    cX
    cD
    vf
    cO
    cJ
    vs
    vb
    dssmapclsntr.o
    dssmapclsntr.d
    cJ
    cX
    dssmapclsntr.x
    topopn
    #
    dssmapf1od
    cJ
    cK
    cX
    dssmapclsntr.x
    dssmapclsntr.k
    clselmap
    @7
    @7
    cK
    cI
    cD
    f1ocnvfv
    syl2anc
    mpd
    @0
    cI
    @1
    cD
    @0
    cX
    cD
    vf
    cO
    cJ
    vs
    vb
    dssmapclsntr.o
    dssmapclsntr.d
    @8
    dssmapnvod
    fveq1d
    eqtr3d
end
