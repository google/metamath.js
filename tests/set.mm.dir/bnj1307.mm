include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "nfcii.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcrii.mm"

theorem bnj1307
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1307.1: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1307.2: |- ( w e. B -> A. x w e. B )

  disjoint B w
  disjoint d w
  disjoint d x
  disjoint w x
  disjoint f x
  assert |- ( w e. C -> A. x w e. C )

  proof
    vx
    vw
    cC
    vx
    cC
    vf
    cv
    #
    vd
    cv
    #
    wfn
    #
    vx
    cv
    @0
    cfv
    cY
    cG
    cfv
    wceq
    #
    vx
    @1
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1307.1
    @6
    vx
    vf
    @5
    vx
    vd
    cB
    vx
    vw
    cB
    bnj1307.2
    nfcii
    @2
    @4
    vx
    @2
    vx
    nfv
    @3
    vx
    @1
    nfra1
    nfan
    nfrex
    nfab
    nfcxfr
    nfcrii
end
