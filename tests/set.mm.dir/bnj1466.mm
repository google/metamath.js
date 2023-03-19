include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "bnj1317.mm"
include "nfcii.mm"
include "nfuni.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "cres.mm"
include "nfres.mm"
include "nfop.mm"
include "nffv.mm"
include "nfsn.mm"
include "nfun.mm"
include "nfcrii.mm"

theorem bnj1466
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1466.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1466.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1466.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1466.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1466.5: |- D = { x e. A | -. E. f ta }
  assume bnj1466.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1466.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1466.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1466.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1466.10: |- P = U. H
  assume bnj1466.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1466.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )

  disjoint A f
  disjoint A w
  disjoint f w
  disjoint G f
  disjoint G w
  disjoint H w
  disjoint P w
  disjoint R f
  disjoint R w
  disjoint Z w
  disjoint f x
  disjoint w x
  assert |- ( w e. Q -> A. f w e. Q )

  proof
    vf
    vw
    cQ
    vf
    cQ
    cP
    vx
    cv
    #
    cZ
    cG
    cfv
    #
    cop
    #
    csn
    #
    cun
    bnj1466.12
    vf
    cP
    @3
    vf
    cP
    cH
    cuni
    bnj1466.10
    vf
    cH
    vf
    vw
    cH
    bnjwtam
    vy
    cA
    cR
    @0
    c-bnj14
    #
    wrex
    vf
    vw
    cH
    bnj1466.9
    bnj1317
    nfcii
    nfuni
    nfcxfr
    #
    vf
    @2
    vf
    @0
    @1
    vf
    @0
    nfcv
    #
    vf
    cZ
    cG
    vf
    cG
    nfcv
    vf
    cZ
    @0
    cP
    @4
    cres
    #
    cop
    bnj1466.11
    vf
    @0
    @7
    @6
    vf
    cP
    @4
    @5
    vf
    @4
    nfcv
    nfres
    nfop
    nfcxfr
    nffv
    nfop
    nfsn
    nfun
    nfcxfr
    nfcrii
end
