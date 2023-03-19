include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "c-bnj18.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "nfan.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nf5ri.mm"

theorem bnj1444
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wrh: wff rh
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
  assume bnj1444.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1444.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1444.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1444.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1444.5: |- D = { x e. A | -. E. f ta }
  assume bnj1444.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1444.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1444.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1444.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1444.10: |- P = U. H
  assume bnj1444.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1444.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1444.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1444.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1444.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1444.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1444.17: |- ( th <-> ( ch /\ z e. E ) )
  assume bnj1444.18: |- ( et <-> ( th /\ z e. { x } ) )
  assume bnj1444.19: |- ( ze <-> ( th /\ z e. _trCl ( x , A , R ) ) )
  assume bnj1444.20: |- ( rh <-> ( ze /\ f e. H /\ z e. dom f ) )

  disjoint A y
  disjoint D y
  disjoint E y
  disjoint R y
  disjoint f y
  disjoint ps y
  disjoint x y
  disjoint y z
  assert |- ( rh -> A. y rh )

  proof
    wrh
    vy
    wrh
    wze
    vf
    cv
    #
    cH
    wcel
    #
    vz
    cv
    #
    @0
    cdm
    wcel
    #
    w3a
    vy
    bnj1444.20
    wze
    @1
    @3
    vy
    wze
    wth
    @2
    cA
    cR
    vx
    cv
    #
    c-bnj18
    wcel
    #
    wa
    vy
    bnj1444.19
    wth
    @5
    vy
    wth
    wch
    @2
    cE
    wcel
    #
    wa
    vy
    bnj1444.17
    wch
    @6
    vy
    wch
    wps
    @4
    cD
    wcel
    #
    vy
    cv
    @4
    cR
    wbr
    wn
    #
    vy
    cD
    wral
    #
    w3a
    vy
    bnj1444.7
    wps
    @7
    @9
    vy
    wps
    vy
    nfv
    @7
    vy
    nfv
    @8
    vy
    cD
    nfra1
    nf3an
    nfxfr
    @6
    vy
    nfv
    nfan
    nfxfr
    @5
    vy
    nfv
    nfan
    nfxfr
    vy
    vf
    cH
    vy
    cH
    bnjwtam
    vy
    cA
    cR
    @4
    c-bnj14
    #
    wrex
    #
    vf
    cab
    bnj1444.9
    @11
    vy
    vf
    bnjwtam
    vy
    @10
    nfre1
    nfab
    nfcxfr
    nfcri
    @3
    vy
    nfv
    nf3an
    nfxfr
    nf5ri
end
