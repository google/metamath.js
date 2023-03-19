include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "cab.mm"
include "nfcv.mm"
include "wsbc.mm"
include "wcel.mm"
include "cdm.mm"
include "c-bnj18.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "wral.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfv.mm"
include "nfan.mm"
include "nfxfr.mm"
include "nfsbc.mm"
include "nfrex.mm"
include "nfuni.mm"
include "cres.mm"
include "nfres.mm"
include "nfop.mm"
include "nffv.mm"
include "nfsn.mm"
include "nfun.mm"
include "nfcrii.mm"

theorem bnj1467
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
  assume bnj1467.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1467.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1467.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1467.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1467.5: |- D = { x e. A | -. E. f ta }
  assume bnj1467.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1467.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1467.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1467.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1467.10: |- P = U. H
  assume bnj1467.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1467.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )

  disjoint A d
  disjoint A w
  disjoint A x
  disjoint d w
  disjoint d x
  disjoint w x
  disjoint B f
  disjoint C w
  disjoint G d
  disjoint G w
  disjoint H w
  disjoint P w
  disjoint R d
  disjoint R w
  disjoint R x
  disjoint Z w
  disjoint d f
  disjoint f w
  disjoint f x
  disjoint d y
  disjoint x y
  assert |- ( w e. Q -> A. d w e. Q )

  proof
    vd
    vw
    cQ
    vd
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
    bnj1467.12
    vd
    cP
    @3
    vd
    cP
    cH
    cuni
    bnj1467.10
    vd
    cH
    vd
    cH
    bnjwtam
    vy
    cA
    cR
    @0
    c-bnj14
    #
    wrex
    #
    vf
    cab
    bnj1467.9
    @5
    vd
    vf
    bnjwtam
    vd
    vy
    @4
    vd
    @4
    nfcv
    #
    bnjwtam
    wta
    vx
    vy
    cv
    #
    wsbc
    vd
    bnj1467.8
    wta
    vd
    vx
    @7
    vd
    @7
    nfcv
    wta
    vf
    cv
    #
    cC
    wcel
    #
    @8
    cdm
    @0
    csn
    cA
    cR
    @0
    c-bnj18
    cun
    wceq
    #
    wa
    vd
    bnj1467.4
    @9
    @10
    vd
    vd
    vf
    cC
    vd
    cC
    @8
    vd
    cv
    #
    wfn
    @0
    @8
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @11
    wral
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1467.3
    @13
    vd
    vf
    @12
    vd
    cB
    nfre1
    nfab
    nfcxfr
    nfcri
    @10
    vd
    nfv
    nfan
    nfxfr
    nfsbc
    nfxfr
    nfrex
    nfab
    nfcxfr
    nfuni
    nfcxfr
    #
    vd
    @2
    vd
    @0
    @1
    vd
    @0
    nfcv
    #
    vd
    cZ
    cG
    vd
    cG
    nfcv
    vd
    cZ
    @0
    cP
    @4
    cres
    #
    cop
    bnj1467.11
    vd
    @0
    @16
    @15
    vd
    cP
    @4
    @14
    @6
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
