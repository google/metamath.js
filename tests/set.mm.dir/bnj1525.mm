include "wne.mm"
include "wa.mm"
include "w-bnj15.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "cuni.mm"
include "bnj1309.mm"
include "bnj1307.mm"
include "nfcii.mm"
include "nfuni.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfne.mm"
include "nfan.mm"
include "nf5ri.mm"

theorem bnj1525
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
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let vw: setvar w
  assume bnj1525.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1525.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1525.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1525.4: |- F = U. C
  assume bnj1525.5: |- ( ph <-> ( R _FrSe A /\ H Fn A /\ A. x e. A ( H ` x ) = ( G ` <. x , ( H |` _pred ( x , A , R ) ) >. ) ) )
  assume bnj1525.6: |- ( ps <-> ( ph /\ F =/= H ) )

  disjoint A x
  disjoint H x
  disjoint R x
  disjoint d x
  disjoint f x
  disjoint B w
  disjoint C w
  disjoint F w
  disjoint H w
  disjoint w x
  disjoint d w
  assert |- ( ps -> A. x ps )

  proof
    wps
    vx
    wps
    wph
    cF
    cH
    wne
    #
    wa
    vx
    bnj1525.6
    wph
    @0
    vx
    wph
    cA
    cR
    w-bnj15
    #
    cH
    cA
    wfn
    #
    vx
    cv
    #
    cH
    cfv
    @3
    cH
    cA
    cR
    @3
    c-bnj14
    cres
    cop
    cG
    cfv
    wceq
    #
    vx
    cA
    wral
    #
    w3a
    vx
    bnj1525.5
    @1
    @2
    @5
    vx
    @1
    vx
    nfv
    @2
    vx
    nfv
    @4
    vx
    cA
    nfra1
    nf3an
    nfxfr
    vx
    cF
    cH
    vx
    cF
    cC
    cuni
    bnj1525.4
    vx
    cC
    vx
    vw
    cC
    vx
    vw
    cB
    cC
    vf
    cG
    cY
    vd
    bnj1525.3
    vx
    vw
    cA
    cB
    cR
    vd
    bnj1525.1
    bnj1309
    bnj1307
    nfcii
    nfuni
    nfcxfr
    vx
    cH
    nfcv
    nfne
    nfan
    nfxfr
    nf5ri
end
