include "cv.mm"
include "cfi.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "sseq12d.mm"
include "elrab2.mm"

theorem ispisys
  let cP: class P
  let cS: class S
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume ispisys.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }

  disjoint O s
  disjoint S s
  disjoint O t
  disjoint O x
  disjoint O y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint P t
  assert |- ( S e. P <-> ( S e. ~P ~P O /\ ( fi ` S ) C_ S ) )

  proof
    vs
    cv
    #
    cfi
    cfv
    #
    @0
    wss
    cS
    cfi
    cfv
    #
    cS
    wss
    vs
    cS
    cO
    cpw
    cpw
    cP
    @0
    cS
    wceq
    #
    @1
    @2
    @0
    cS
    @0
    cS
    cfi
    fveq2
    @3
    id
    sseq12d
    ispisys.p
    elrab2
end
