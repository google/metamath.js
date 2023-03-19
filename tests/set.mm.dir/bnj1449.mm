include "cv.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "nfv.mm"
include "wex.mm"
include "crab.mm"
include "nfe1.mm"
include "nfn.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfne.mm"
include "nfan.mm"
include "nfxfr.mm"
include "nfcri.mm"
include "nfral.mm"
include "nf3an.mm"
include "nf5ri.mm"

theorem bnj1449
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
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
  let cE: class E
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1449.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1449.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1449.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1449.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1449.5: |- D = { x e. A | -. E. f ta }
  assume bnj1449.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1449.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1449.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1449.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1449.10: |- P = U. H
  assume bnj1449.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1449.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1449.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1449.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1449.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1449.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1449.17: |- ( th <-> ( ch /\ z e. E ) )
  assume bnj1449.18: |- ( et <-> ( th /\ z e. { x } ) )
  assume bnj1449.19: |- ( ze <-> ( th /\ z e. _trCl ( x , A , R ) ) )

  disjoint A f
  disjoint E f
  disjoint R f
  disjoint f x
  disjoint f y
  disjoint f z
  assert |- ( ze -> A. f ze )

  proof
    wze
    vf
    wze
    wth
    vz
    cv
    #
    cA
    cR
    vx
    cv
    #
    c-bnj18
    wcel
    #
    wa
    vf
    bnj1449.19
    wth
    @2
    vf
    wth
    wch
    @0
    cE
    wcel
    #
    wa
    vf
    bnj1449.17
    wch
    @3
    vf
    wch
    wps
    @1
    cD
    wcel
    #
    vy
    cv
    @1
    cR
    wbr
    wn
    #
    vy
    cD
    wral
    #
    w3a
    vf
    bnj1449.7
    wps
    @4
    @6
    vf
    wps
    cA
    cR
    w-bnj15
    #
    cD
    c0
    wne
    #
    wa
    vf
    bnj1449.6
    @7
    @8
    vf
    @7
    vf
    nfv
    vf
    cD
    c0
    vf
    cD
    wta
    vf
    wex
    #
    wn
    #
    vx
    cA
    crab
    bnj1449.5
    @10
    vf
    vx
    cA
    @9
    vf
    wta
    vf
    nfe1
    nfn
    vf
    cA
    nfcv
    nfrab
    nfcxfr
    #
    vf
    c0
    nfcv
    nfne
    nfan
    nfxfr
    vf
    vx
    cD
    @11
    nfcri
    @5
    vf
    vy
    cD
    @11
    @5
    vf
    nfv
    nfral
    nf3an
    nfxfr
    @3
    vf
    nfv
    nfan
    nfxfr
    @2
    vf
    nfv
    nfan
    nfxfr
    nf5ri
end
