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
include "nfcv.mm"
include "wsbc.mm"
include "wcel.mm"
include "cdm.mm"
include "c-bnj18.mm"
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
include "nfeq.mm"
include "nf5ri.mm"

theorem bnj1446
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
  assume bnj1446.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1446.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1446.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1446.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1446.5: |- D = { x e. A | -. E. f ta }
  assume bnj1446.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1446.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1446.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1446.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1446.10: |- P = U. H
  assume bnj1446.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1446.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1446.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.

  disjoint A d
  disjoint A x
  disjoint d x
  disjoint B f
  disjoint G d
  disjoint R d
  disjoint R x
  disjoint d f
  disjoint f x
  disjoint d y
  disjoint x y
  disjoint d z
  assert |- ( ( Q ` z ) = ( G ` W ) -> A. d ( Q ` z ) = ( G ` W ) )

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
    vd
    vd
    @1
    @2
    vd
    @0
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
    bnj1446.12
    vd
    cP
    @6
    vd
    cP
    cH
    cuni
    bnj1446.10
    vd
    cH
    vd
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
    bnj1446.9
    @8
    vd
    vf
    bnjwtam
    vd
    vy
    @7
    vd
    @7
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
    bnj1446.8
    wta
    vd
    vx
    @10
    vd
    @10
    nfcv
    wta
    vf
    cv
    #
    cC
    wcel
    #
    @11
    cdm
    @3
    csn
    cA
    cR
    @3
    c-bnj18
    cun
    wceq
    #
    wa
    vd
    bnj1446.4
    @12
    @13
    vd
    vd
    vf
    cC
    vd
    cC
    @11
    vd
    cv
    #
    wfn
    @3
    @11
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @14
    wral
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1446.3
    @16
    vd
    vf
    @15
    vd
    cB
    nfre1
    nfab
    nfcxfr
    nfcri
    @13
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
    @5
    vd
    @3
    @4
    vd
    @3
    nfcv
    #
    vd
    cZ
    cG
    vd
    cG
    nfcv
    #
    vd
    cZ
    @3
    cP
    @7
    cres
    #
    cop
    bnj1446.11
    vd
    @3
    @20
    @18
    vd
    cP
    @7
    @17
    @9
    nfres
    nfop
    nfcxfr
    nffv
    nfop
    nfsn
    nfun
    nfcxfr
    #
    vd
    @0
    nfcv
    #
    nffv
    vd
    cW
    cG
    @19
    vd
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
    bnj1446.13
    vd
    @0
    @24
    @22
    vd
    cQ
    @23
    @21
    vd
    @23
    nfcv
    nfres
    nfop
    nfcxfr
    nffv
    nfeq
    nf5ri
end
