include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "vex.mm"
include "fvex.mm"
include "funsn.mm"
include "jctir.mm"
include "c-bnj18.mm"
include "dmsnop.mm"
include "a1i.mm"
include "ineq12d.mm"
include "w-bnj15.mm"
include "wral.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "simplbi.mm"
include "bnj835.mm"
include "wsbc.mm"
include "wi.mm"
include "w3a.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1417.mm"
include "disjsn.mm"
include "ralbii.mm"
include "sylibr.mm"
include "syl.mm"
include "wex.mm"
include "bnj1212.mm"
include "bnj1294.mm"
include "eqtrd.mm"
include "funun.mm"
include "syl2anc.mm"
include "funeqi.mm"

theorem bnj1421
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
  let vz: setvar z
  assume bnj1421.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1421.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1421.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1421.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1421.5: |- D = { x e. A | -. E. f ta }
  assume bnj1421.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1421.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1421.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1421.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1421.10: |- P = U. H
  assume bnj1421.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1421.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1421.13: |- ( ch -> Fun P )
  assume bnj1421.14: |- ( ch -> dom Q = ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1421.15: |- ( ch -> dom P = _trCl ( x , A , R ) )

  disjoint A x
  disjoint R x
  disjoint A z
  disjoint x z
  disjoint R z
  assert |- ( ch -> Fun Q )

  proof
    wch
    cP
    vx
    cv
    #
    cZ
    cG
    cfv
    #
    cop
    csn
    #
    cun
    #
    wfun
    #
    cQ
    wfun
    wch
    cP
    wfun
    #
    @2
    wfun
    #
    wa
    cP
    cdm
    #
    @2
    cdm
    #
    cin
    #
    c0
    wceq
    @4
    wch
    @5
    @6
    bnj1421.13
    @0
    @1
    vx
    vex
    cZ
    cG
    fvex
    #
    funsn
    jctir
    wch
    @9
    cA
    cR
    @0
    c-bnj18
    #
    @0
    csn
    #
    cin
    #
    c0
    wch
    @7
    @11
    @8
    @12
    bnj1421.15
    @8
    @12
    wceq
    wch
    @0
    @1
    @10
    dmsnop
    a1i
    ineq12d
    wch
    @13
    c0
    wceq
    #
    vx
    cA
    wch
    cA
    cR
    w-bnj15
    #
    @14
    vx
    cA
    wral
    #
    wps
    @0
    cD
    wcel
    vy
    cv
    @0
    cR
    wbr
    wn
    vy
    cD
    wral
    #
    @15
    wch
    bnj1421.7
    wps
    @15
    cD
    c0
    wne
    bnj1421.6
    simplbi
    bnj835
    @15
    @0
    @11
    wcel
    wn
    #
    vx
    cA
    wral
    @16
    @15
    @18
    vz
    cv
    #
    @0
    cR
    wbr
    @18
    vx
    @19
    wsbc
    wi
    vz
    cA
    wral
    #
    @15
    @0
    cA
    wcel
    @20
    w3a
    #
    vx
    vz
    cA
    cA
    cR
    @0
    c-bnj14
    #
    vz
    @22
    cA
    cR
    @19
    c-bnj18
    ciun
    cun
    #
    cR
    @15
    biid
    @18
    biid
    @20
    biid
    @21
    biid
    @23
    eqid
    bnj1417
    @14
    @18
    vx
    cA
    @11
    @0
    disjsn
    ralbii
    sylibr
    syl
    wta
    vf
    wex
    wn
    wps
    wch
    @17
    vx
    cA
    cD
    bnj1421.5
    bnj1421.7
    bnj1212
    bnj1294
    eqtrd
    cP
    @2
    funun
    syl2anc
    cQ
    @3
    bnj1421.12
    funeqi
    sylibr
end
