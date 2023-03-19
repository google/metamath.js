include "cv.mm"
include "c-bnj14.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "nfv.mm"
include "wex.mm"
include "crab.mm"
include "wfn.mm"
include "cfv.mm"
include "wrex.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfxfr.mm"
include "nfex.mm"
include "nfn.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfne.mm"
include "nfral.mm"
include "nf3an.mm"
include "nf5ri.mm"
include "bnj1351.mm"
include "nf5i.mm"
include "wsbc.mm"
include "nfsbc.mm"
include "nfrex.mm"
include "ax-5.mm"
include "bnj982.mm"
include "hbxfrbi.mm"

theorem bnj1445
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1445.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1445.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1445.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1445.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1445.5: |- D = { x e. A | -. E. f ta }
  assume bnj1445.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1445.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1445.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1445.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1445.10: |- P = U. H
  assume bnj1445.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1445.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1445.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1445.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1445.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1445.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1445.17: |- ( th <-> ( ch /\ z e. E ) )
  assume bnj1445.18: |- ( et <-> ( th /\ z e. { x } ) )
  assume bnj1445.19: |- ( ze <-> ( th /\ z e. _trCl ( x , A , R ) ) )
  assume bnj1445.20: |- ( rh <-> ( ze /\ f e. H /\ z e. dom f ) )
  assume bnj1445.21: |- ( si <-> ( rh /\ y e. _pred ( x , A , R ) /\ f e. C /\ dom f = ( { y } u. _trCl ( y , A , R ) ) ) )
  assume bnj1445.22: |- ( ph <-> ( si /\ d e. B /\ f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) )
  assume bnj1445.23: |- X = <. z , ( f |` _pred ( z , A , R ) ) >.

  disjoint A d
  disjoint A x
  disjoint d x
  disjoint B f
  disjoint E d
  disjoint R d
  disjoint R x
  disjoint d f
  disjoint f x
  disjoint d y
  disjoint x y
  disjoint d z
  assert |- ( si -> A. d si )

  proof
    wsi
    wrh
    vy
    cv
    #
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    wcel
    #
    vf
    cv
    #
    cC
    wcel
    #
    @4
    cdm
    #
    @0
    csn
    cA
    cR
    @0
    c-bnj18
    cun
    wceq
    #
    w-bnj17
    vd
    bnj1445.21
    wrh
    @3
    @5
    @7
    vd
    wrh
    vd
    wrh
    wze
    @4
    cH
    wcel
    #
    vz
    cv
    #
    @6
    wcel
    #
    w3a
    vd
    bnj1445.20
    wze
    @8
    @10
    vd
    wze
    wth
    @9
    cA
    cR
    @1
    c-bnj18
    #
    wcel
    #
    wa
    vd
    bnj1445.19
    wth
    @12
    vd
    wth
    wch
    @9
    cE
    wcel
    #
    wa
    #
    vd
    bnj1445.17
    @14
    vd
    wch
    @13
    vd
    wch
    vd
    wch
    wps
    @1
    cD
    wcel
    #
    @0
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
    vd
    bnj1445.7
    wps
    @15
    @17
    vd
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
    vd
    bnj1445.6
    @18
    @19
    vd
    @18
    vd
    nfv
    vd
    cD
    c0
    vd
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
    bnj1445.5
    @21
    vd
    vx
    cA
    @20
    vd
    wta
    vd
    vf
    wta
    @5
    @6
    @1
    csn
    @11
    cun
    wceq
    #
    wa
    vd
    bnj1445.4
    @5
    @22
    vd
    vd
    vf
    cC
    vd
    cC
    @4
    vd
    cv
    #
    wfn
    @1
    @4
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @23
    wral
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1445.3
    @25
    vd
    vf
    @24
    vd
    cB
    nfre1
    nfab
    nfcxfr
    nfcri
    #
    @22
    vd
    nfv
    nfan
    nfxfr
    #
    nfex
    nfn
    vd
    cA
    nfcv
    nfrab
    nfcxfr
    #
    vd
    c0
    nfcv
    nfne
    nfan
    nfxfr
    vd
    vx
    cD
    @28
    nfcri
    @16
    vd
    vy
    cD
    @28
    @16
    vd
    nfv
    nfral
    nf3an
    nfxfr
    nf5ri
    bnj1351
    nf5i
    nfxfr
    @12
    vd
    nfv
    nfan
    nfxfr
    vd
    vf
    cH
    vd
    cH
    bnjwtam
    vy
    @2
    wrex
    #
    vf
    cab
    bnj1445.9
    @29
    vd
    vf
    bnjwtam
    vd
    vy
    @2
    vd
    @2
    nfcv
    bnjwtam
    wta
    vx
    @0
    wsbc
    vd
    bnj1445.8
    wta
    vd
    vx
    @0
    vd
    @0
    nfcv
    @27
    nfsbc
    nfxfr
    nfrex
    nfab
    nfcxfr
    nfcri
    @10
    vd
    nfv
    nf3an
    nfxfr
    nf5ri
    @3
    vd
    ax-5
    @5
    vd
    @26
    nf5ri
    @7
    vd
    ax-5
    bnj982
    hbxfrbi
end
