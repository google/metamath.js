include "cv.mm"
include "cfv.mm"
include "wceq.mm"
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
include "nfeq.mm"
include "nf5ri.mm"

theorem bnj1448
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
  let vw: setvar w
  assume bnj1448.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1448.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1448.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1448.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1448.5: |- D = { x e. A | -. E. f ta }
  assume bnj1448.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1448.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1448.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1448.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1448.10: |- P = U. H
  assume bnj1448.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1448.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1448.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.

  disjoint A f
  disjoint G f
  disjoint R f
  disjoint f x
  disjoint f z
  disjoint A w
  disjoint f w
  disjoint G w
  disjoint H w
  disjoint P w
  disjoint Q w
  disjoint R w
  disjoint W w
  disjoint Z w
  disjoint w x
  disjoint w z
  assert |- ( ( Q ` z ) = ( G ` W ) -> A. f ( Q ` z ) = ( G ` W ) )

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
    vf
    vf
    @1
    @2
    vf
    @0
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
    bnj1448.12
    vf
    cP
    @6
    vf
    cP
    cH
    cuni
    bnj1448.10
    vf
    cH
    vf
    vw
    cH
    bnjwtam
    vy
    cA
    cR
    @3
    c-bnj14
    #
    wrex
    vf
    vw
    cH
    bnj1448.9
    bnj1317
    nfcii
    nfuni
    nfcxfr
    #
    vf
    @5
    vf
    @3
    @4
    vf
    @3
    nfcv
    #
    vf
    cZ
    cG
    vf
    cG
    nfcv
    #
    vf
    cZ
    @3
    cP
    @7
    cres
    #
    cop
    bnj1448.11
    vf
    @3
    @11
    @9
    vf
    cP
    @7
    @8
    vf
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
    vf
    @0
    nfcv
    #
    nffv
    vf
    cW
    cG
    @10
    vf
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
    bnj1448.13
    vf
    @0
    @15
    @13
    vf
    cQ
    @14
    @12
    vf
    @14
    nfcv
    nfres
    nfop
    nfcxfr
    nffv
    nfeq
    nf5ri
end
