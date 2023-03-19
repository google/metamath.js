include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "nfv.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "nf5ri.mm"

theorem bnj1518
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1518.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1518.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1518.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1518.4: |- F = U. C
  assume bnj1518.5: |- ( ph <-> ( R _FrSe A /\ x e. A ) )
  assume bnj1518.6: |- ( ps <-> ( ph /\ f e. C /\ x e. dom f ) )

  disjoint d f
  disjoint d ph
  disjoint d x
  assert |- ( ps -> A. d ps )

  proof
    wps
    vd
    wps
    wph
    vf
    cv
    #
    cC
    wcel
    #
    vx
    cv
    #
    @0
    cdm
    wcel
    #
    w3a
    vd
    bnj1518.6
    wph
    @1
    @3
    vd
    wph
    vd
    nfv
    vd
    vf
    cC
    vd
    cC
    @0
    vd
    cv
    #
    wfn
    @2
    @0
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @4
    wral
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1518.3
    @6
    vd
    vf
    @5
    vd
    cB
    nfre1
    nfab
    nfcxfr
    nfcri
    @3
    vd
    nfv
    nf3an
    nfxfr
    nf5ri
end
