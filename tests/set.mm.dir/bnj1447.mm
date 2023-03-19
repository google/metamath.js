include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfuni.mm"
include "nfcv.mm"
include "cres.mm"
include "nfres.mm"
include "nfop.mm"
include "nffv.mm"
include "nfsn.mm"
include "nfun.mm"
include "nfeq.mm"
include "nf5ri.mm"

theorem bnj1447
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1447.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1447.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1447.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1447.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1447.5: |- D = { x e. A | -. E. f ta }
  assume bnj1447.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1447.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1447.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1447.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1447.10: |- P = U. H
  assume bnj1447.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1447.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1447.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.

  disjoint A y
  disjoint G y
  disjoint R y
  disjoint x y
  disjoint y z
  assert |- ( ( Q ` z ) = ( G ` W ) -> A. y ( Q ` z ) = ( G ` W ) )

  proof
    vz
    cv
    #
    cQ
    cfv
    #
    cW
    cG
    cfv
    #
    wceq
    vy
    vy
    @1
    @2
    vy
    @0
    cQ
    vy
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
    bnj1447.12
    vy
    cP
    @6
    vy
    cP
    cH
    cuni
    bnj1447.10
    vy
    cH
    vy
    cH
    bnjwtam
    vy
    cA
    cR
    @3
    c-bnj14
    #
    wrex
    #
    vf
    cab
    bnj1447.9
    @8
    vy
    vf
    bnjwtam
    vy
    @7
    nfre1
    nfab
    nfcxfr
    nfuni
    nfcxfr
    #
    vy
    @5
    vy
    @3
    @4
    vy
    @3
    nfcv
    #
    vy
    cZ
    cG
    vy
    cG
    nfcv
    #
    vy
    cZ
    @3
    cP
    @7
    cres
    #
    cop
    bnj1447.11
    vy
    @3
    @12
    @10
    vy
    cP
    @7
    @9
    vy
    @7
    nfcv
    nfres
    nfop
    nfcxfr
    nffv
    nfop
    nfsn
    nfun
    nfcxfr
    #
    vy
    @0
    nfcv
    #
    nffv
    vy
    cW
    cG
    @11
    vy
    cW
    @0
    cQ
    cA
    cR
    @0
    c-bnj14
    #
    cres
    #
    cop
    bnj1447.13
    vy
    @0
    @16
    @14
    vy
    cQ
    @15
    @13
    vy
    @15
    nfcv
    nfres
    nfop
    nfcxfr
    nffv
    nfeq
    nf5ri
end
