include "cv.mm"
include "c-bnj18.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cun.mm"
include "cdm.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "simplbi.mm"
include "bnj835.mm"
include "wex.mm"
include "bnj1212.mm"
include "eqid.mm"
include "bnj1414.mm"
include "syl2anc.mm"
include "csn.mm"
include "iunun.mm"
include "iunid.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "wa.mm"
include "w3a.mm"
include "biid.mm"
include "bnj1398.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"

theorem bnj1415
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let bnjwtam: wff ta'
  let vz: setvar z
  assume bnj1415.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1415.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1415.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1415.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1415.5: |- D = { x e. A | -. E. f ta }
  assume bnj1415.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1415.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1415.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1415.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1415.10: |- P = U. H

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B f
  disjoint C y
  disjoint D y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint d f
  disjoint d x
  disjoint ps y
  disjoint ta y
  disjoint A z
  disjoint f z
  disjoint x z
  disjoint y z
  disjoint H z
  disjoint P z
  disjoint R z
  disjoint ch z
  assert |- ( ch -> dom P = _trCl ( x , A , R ) )

  proof
    wch
    cA
    cR
    vx
    cv
    #
    c-bnj18
    #
    cA
    cR
    @0
    c-bnj14
    #
    vy
    @2
    cA
    cR
    vy
    cv
    #
    c-bnj18
    #
    ciun
    #
    cun
    #
    cP
    cdm
    #
    wch
    cA
    cR
    w-bnj15
    #
    @0
    cA
    wcel
    @1
    @6
    wceq
    wps
    @0
    cD
    wcel
    @3
    @0
    cR
    wbr
    wn
    vy
    cD
    wral
    #
    @8
    wch
    bnj1415.7
    wps
    @8
    cD
    c0
    wne
    bnj1415.6
    simplbi
    bnj835
    wta
    vf
    wex
    wn
    wps
    wch
    @9
    vx
    cA
    cD
    bnj1415.5
    bnj1415.7
    bnj1212
    vy
    cA
    @6
    cR
    @0
    @6
    eqid
    bnj1414
    syl2anc
    wch
    @6
    vy
    @2
    @3
    csn
    #
    @4
    cun
    #
    ciun
    #
    @7
    @12
    vy
    @2
    @10
    ciun
    #
    @5
    cun
    @6
    vy
    @2
    @10
    @4
    iunun
    @13
    @2
    @5
    vy
    @2
    iunid
    uneq1i
    eqtri
    wps
    wch
    wch
    vz
    cv
    #
    @12
    wcel
    wa
    #
    wta
    @15
    @3
    @2
    wcel
    @14
    @11
    wcel
    w3a
    #
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cR
    vf
    cG
    cH
    cY
    vd
    bnjwtam
    bnj1415.1
    bnj1415.2
    bnj1415.3
    bnj1415.4
    bnj1415.5
    bnj1415.6
    bnj1415.7
    bnj1415.8
    bnj1415.9
    bnj1415.10
    @15
    biid
    @16
    biid
    bnj1398
    syl5eqr
    eqtr2d
end
