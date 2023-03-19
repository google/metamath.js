include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wex.mm"
include "bnj1466.mm"
include "nfcii.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "bnj1317.mm"
include "nfel.mm"
include "nfdm.mm"
include "nfeq1.mm"
include "nfan.mm"
include "eleq1.mm"
include "dmeq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spcegf.mm"
include "mpan9.mm"

theorem bnj1491
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
  let cQ: class Q
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  let vw: setvar w
  assume bnj1491.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1491.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1491.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1491.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1491.5: |- D = { x e. A | -. E. f ta }
  assume bnj1491.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1491.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1491.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1491.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1491.10: |- P = U. H
  assume bnj1491.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1491.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1491.13: |- ( ch -> ( Q e. C /\ dom Q = ( { x } u. _trCl ( x , A , R ) ) ) )

  disjoint A f
  disjoint G f
  disjoint R f
  disjoint f x
  disjoint A w
  disjoint f w
  disjoint C w
  disjoint G w
  disjoint H w
  disjoint P w
  disjoint Q w
  disjoint R w
  disjoint Z w
  disjoint w x
  assert |- ( ( ch /\ Q e. _V ) -> E. f ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )

  proof
    wch
    cQ
    cC
    wcel
    #
    cQ
    cdm
    #
    vx
    cv
    #
    csn
    cA
    cR
    @2
    c-bnj18
    cun
    #
    wceq
    #
    wa
    #
    cQ
    cvv
    wcel
    vf
    cv
    #
    cC
    wcel
    #
    @6
    cdm
    #
    @3
    wceq
    #
    wa
    #
    vf
    wex
    bnj1491.13
    @10
    @5
    vf
    cQ
    cvv
    vf
    vw
    cQ
    wps
    wch
    wta
    vx
    vy
    vw
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cG
    cH
    cY
    cZ
    vd
    bnjwtam
    bnj1491.1
    bnj1491.2
    bnj1491.3
    bnj1491.4
    bnj1491.5
    bnj1491.6
    bnj1491.7
    bnj1491.8
    bnj1491.9
    bnj1491.10
    bnj1491.11
    bnj1491.12
    bnj1466
    nfcii
    #
    @0
    @4
    vf
    vf
    cQ
    cC
    @11
    vf
    vw
    cC
    @6
    vd
    cv
    #
    wfn
    @2
    @6
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @12
    wral
    wa
    vd
    cB
    wrex
    vf
    vw
    cC
    bnj1491.3
    bnj1317
    nfcii
    nfel
    vf
    @1
    @3
    vf
    cQ
    @11
    nfdm
    nfeq1
    nfan
    @6
    cQ
    wceq
    #
    @7
    @0
    @9
    @4
    @6
    cQ
    cC
    eleq1
    @13
    @8
    @1
    @3
    @6
    cQ
    dmeq
    eqeq1d
    anbi12d
    spcegf
    mpan9
end
