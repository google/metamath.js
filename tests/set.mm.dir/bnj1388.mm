include "wex.mm"
include "cv.mm"
include "c-bnj14.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "wa.mm"
include "bnj1152.mm"
include "simplbi.mm"
include "adantl.mm"
include "wi.mm"
include "biimpi.mm"
include "simprd.mm"
include "simp3bi.mm"
include "adantr.mm"
include "wal.mm"
include "df-ral.mm"
include "con2b.mm"
include "albii.mm"
include "bitri.mm"
include "sp.mm"
include "impcom.mm"
include "sylan2b.mm"
include "syl2anc.mm"
include "crab.mm"
include "eleq2i.mm"
include "nfcv.mm"
include "wsbc.mm"
include "nfsbc1v.mm"
include "nfex.mm"
include "nfn.mm"
include "weq.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "notbid.mm"
include "elrabf.mm"
include "sylnib.mm"
include "iman.mm"
include "sylibr.mm"
include "mpd.mm"
include "ex.mm"
include "ralrimi.mm"

theorem bnj1388
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1388.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1388.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1388.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1388.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1388.5: |- D = { x e. A | -. E. f ta }
  assume bnj1388.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1388.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1388.8: |- ( ta' <-> [. y / x ]. ta )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B f
  disjoint D y
  disjoint R x
  disjoint R y
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint f y
  disjoint ps y
  disjoint ta y
  assert |- ( ch -> A. y e. _pred ( x , A , R ) E. f ta' )

  proof
    wch
    bnjwtam
    vf
    wex
    #
    vy
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    wch
    wps
    @1
    cD
    wcel
    #
    vy
    cv
    #
    @1
    cR
    wbr
    #
    wn
    #
    vy
    cD
    wral
    #
    w3a
    vy
    bnj1388.7
    wps
    @3
    @7
    vy
    wps
    vy
    nfv
    @3
    vy
    nfv
    @6
    vy
    cD
    nfra1
    nf3an
    nfxfr
    wch
    @4
    @2
    wcel
    #
    @0
    wch
    @8
    wa
    #
    @4
    cA
    wcel
    #
    @0
    @8
    @10
    wch
    @8
    @10
    @5
    cA
    cR
    @1
    @4
    bnj1152
    #
    simplbi
    adantl
    @9
    @10
    @0
    wn
    #
    wa
    #
    wn
    @10
    @0
    wi
    @9
    @4
    cD
    wcel
    #
    @13
    @9
    @5
    @7
    @14
    wn
    #
    @9
    @10
    @5
    @8
    @10
    @5
    wa
    #
    wch
    @8
    @16
    @11
    biimpi
    adantl
    simprd
    wch
    @7
    @8
    wch
    wps
    @3
    @7
    bnj1388.7
    simp3bi
    adantr
    @7
    @5
    @5
    @15
    wi
    #
    vy
    wal
    #
    @15
    @7
    @14
    @6
    wi
    #
    vy
    wal
    @18
    @6
    vy
    cD
    df-ral
    @19
    @17
    vy
    @14
    @5
    con2b
    albii
    bitri
    @18
    @5
    @15
    @17
    vy
    sp
    impcom
    sylan2b
    syl2anc
    @14
    @4
    wta
    vf
    wex
    #
    wn
    #
    vx
    cA
    crab
    #
    wcel
    @13
    cD
    @22
    @4
    bnj1388.5
    eleq2i
    @21
    @12
    vx
    @4
    cA
    vx
    @4
    nfcv
    vx
    cA
    nfcv
    @0
    vx
    bnjwtam
    vx
    vf
    bnjwtam
    wta
    vx
    @4
    wsbc
    #
    vx
    bnj1388.8
    wta
    vx
    @4
    nfsbc1v
    nfxfr
    nfex
    nfn
    vx
    vy
    weq
    #
    @20
    @0
    @24
    wta
    bnjwtam
    vf
    @24
    wta
    @23
    bnjwtam
    wta
    vx
    @4
    sbceq1a
    bnj1388.8
    syl6bbr
    exbidv
    notbid
    elrabf
    bitri
    sylnib
    @10
    @0
    iman
    sylibr
    mpd
    ex
    ralrimi
end
