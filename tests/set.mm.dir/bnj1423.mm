include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "c-bnj18.mm"
include "biid.mm"
include "bnj1442.mm"
include "cdm.mm"
include "w3a.mm"
include "c-bnj14.mm"
include "cun.mm"
include "w-bnj17.mm"
include "wfn.mm"
include "wral.mm"
include "cres.mm"
include "cop.mm"
include "eqid.mm"
include "bnj1450.mm"
include "wo.mm"
include "bnj1424.mm"
include "adantl.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"

theorem bnj1423
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
  let cE: class E
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1423.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1423.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1423.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1423.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1423.5: |- D = { x e. A | -. E. f ta }
  assume bnj1423.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1423.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1423.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1423.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1423.10: |- P = U. H
  assume bnj1423.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1423.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1423.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1423.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1423.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1423.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint D y
  disjoint E d
  disjoint E f
  disjoint E y
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y z
  disjoint ch z
  disjoint ps y
  assert |- ( ch -> A. z e. E ( Q ` z ) = ( G ` W ) )

  proof
    wch
    vz
    cv
    #
    cQ
    cfv
    cW
    cG
    cfv
    wceq
    #
    vz
    cE
    wch
    @0
    cE
    wcel
    #
    wa
    #
    @0
    vx
    cv
    #
    csn
    #
    wcel
    #
    @1
    @0
    cA
    cR
    @4
    c-bnj18
    #
    wcel
    #
    wps
    wch
    @3
    wta
    @3
    @6
    wa
    #
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1423.1
    bnj1423.2
    bnj1423.3
    bnj1423.4
    bnj1423.5
    bnj1423.6
    bnj1423.7
    bnj1423.8
    bnj1423.9
    bnj1423.10
    bnj1423.11
    bnj1423.12
    bnj1423.13
    bnj1423.14
    bnj1423.15
    bnj1423.16
    @3
    biid
    #
    @9
    biid
    #
    bnj1442
    @3
    @8
    wa
    #
    vf
    cv
    #
    cH
    wcel
    @0
    @13
    cdm
    #
    wcel
    w3a
    #
    vy
    cv
    #
    cA
    cR
    @4
    c-bnj14
    wcel
    @13
    cC
    wcel
    @14
    @16
    csn
    cA
    cR
    @16
    c-bnj18
    cun
    wceq
    w-bnj17
    #
    vd
    cv
    #
    cB
    wcel
    @13
    @18
    wfn
    @4
    @13
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @18
    wral
    w-bnj17
    #
    wps
    wch
    @3
    wta
    @9
    @12
    @17
    @15
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cE
    cG
    cH
    cW
    @0
    @13
    cA
    cR
    @0
    c-bnj14
    cres
    cop
    #
    cY
    cZ
    vd
    bnjwtam
    bnj1423.1
    bnj1423.2
    bnj1423.3
    bnj1423.4
    bnj1423.5
    bnj1423.6
    bnj1423.7
    bnj1423.8
    bnj1423.9
    bnj1423.10
    bnj1423.11
    bnj1423.12
    bnj1423.13
    bnj1423.14
    bnj1423.15
    bnj1423.16
    @10
    @11
    @12
    biid
    @15
    biid
    @17
    biid
    @19
    biid
    @20
    eqid
    bnj1450
    @2
    @6
    @8
    wo
    wch
    cE
    @5
    @7
    @0
    bnj1423.14
    bnj1424
    adantl
    mpjaodan
    ralrimiva
end
