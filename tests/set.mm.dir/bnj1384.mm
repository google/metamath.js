include "w-bnj15.mm"
include "cuni.mm"
include "wfun.mm"
include "cv.mm"
include "wral.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "bnj1373.mm"
include "bnj1371.mm"
include "rgen.mm"
include "wcel.mm"
include "id.mm"
include "bnj1374.mm"
include "wi.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "cab.mm"
include "nfab1.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "wfn.mm"
include "cfv.mm"
include "wa.mm"
include "nfim.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "chvar.mm"
include "eqid.mm"
include "bnj1326.mm"
include "syl3an.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "biid.mm"
include "bnj1317.mm"
include "bnj1386.mm"
include "sylancr.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem bnj1384
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
  let vg: setvar g
  assume bnj1384.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1384.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1384.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1384.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1384.5: |- D = { x e. A | -. E. f ta }
  assume bnj1384.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1384.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1384.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1384.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1384.10: |- P = U. H

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint C y
  disjoint G d
  disjoint G f
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint f y
  disjoint x y
  disjoint A z
  disjoint d z
  disjoint f z
  disjoint x z
  disjoint A g
  disjoint f g
  disjoint C g
  disjoint H g
  disjoint H z
  disjoint g z
  disjoint R g
  assert |- ( R _FrSe A -> Fun P )

  proof
    cA
    cR
    w-bnj15
    #
    cH
    cuni
    #
    wfun
    #
    cP
    wfun
    @0
    vf
    cv
    #
    wfun
    #
    vf
    cH
    wral
    #
    @3
    @3
    cdm
    vg
    cv
    #
    cdm
    cin
    #
    cres
    @6
    @7
    cres
    wceq
    #
    vg
    cH
    wral
    vf
    cH
    wral
    #
    @2
    @4
    vf
    cH
    wps
    wch
    wta
    vx
    vy
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
    bnj1384.1
    bnj1384.2
    bnj1384.3
    bnj1384.4
    bnj1384.5
    bnj1384.6
    bnj1384.7
    bnj1384.8
    bnj1384.9
    bnj1384.10
    wta
    vx
    vy
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnjwtam
    bnj1384.1
    bnj1384.2
    bnj1384.3
    bnj1384.4
    bnj1384.8
    bnj1373
    bnj1371
    rgen
    @0
    @8
    vf
    vg
    cH
    cH
    @0
    @3
    cH
    wcel
    #
    @6
    cH
    wcel
    #
    @8
    @0
    @0
    @10
    @3
    cC
    wcel
    #
    @11
    @6
    cC
    wcel
    #
    @8
    @0
    id
    wps
    wch
    wta
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    vf
    cG
    cH
    cY
    vd
    bnjwtam
    bnj1384.1
    bnj1384.2
    bnj1384.3
    bnj1384.4
    bnj1384.5
    bnj1384.6
    bnj1384.7
    bnj1384.8
    bnj1384.9
    bnj1374
    #
    @10
    @12
    wi
    @11
    @13
    wi
    vf
    vg
    @11
    @13
    vf
    vf
    vg
    cH
    vf
    cH
    bnjwtam
    vy
    cA
    cR
    vx
    cv
    #
    c-bnj14
    wrex
    #
    vf
    cab
    bnj1384.9
    @16
    vf
    nfab1
    nfcxfr
    nfcri
    vf
    vg
    cC
    vf
    cC
    @3
    vd
    cv
    #
    wfn
    @15
    @3
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @17
    wral
    wa
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1384.3
    @18
    vf
    nfab1
    nfcxfr
    nfcri
    nfim
    @3
    @6
    wceq
    @10
    @11
    @12
    @13
    @3
    @6
    cH
    eleq1
    @3
    @6
    cC
    eleq1
    imbi12d
    @14
    chvar
    vx
    cA
    cB
    cC
    @7
    cR
    vf
    vf
    vg
    cG
    cY
    vd
    bnj1384.1
    bnj1384.2
    bnj1384.3
    @7
    eqid
    #
    bnj1326
    syl3an
    3expib
    ralrimivv
    @5
    @5
    @9
    wa
    #
    vz
    cH
    @7
    vf
    vg
    @5
    biid
    @19
    @20
    biid
    @16
    vf
    vz
    cH
    bnj1384.9
    bnj1317
    bnj1386
    sylancr
    cP
    @1
    bnj1384.10
    funeqi
    sylibr
end
