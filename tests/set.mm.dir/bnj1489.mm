include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "cuni.mm"
include "wcel.mm"
include "c-bnj14.mm"
include "weu.mm"
include "wral.mm"
include "wrex.mm"
include "cab.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "w-bnj13.mm"
include "bnj1364.mm"
include "df-bnj13.mm"
include "sylib.mm"
include "bnj832.mm"
include "bnj835.mm"
include "wex.mm"
include "bnj1212.mm"
include "bnj1294.mm"
include "w3a.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "wa.mm"
include "simplbi.mm"
include "adantr.mm"
include "bnj1388.mm"
include "r19.21bi.mm"
include "cdm.mm"
include "c-bnj18.mm"
include "wi.mm"
include "wsbc.mm"
include "nfsbc1v.mm"
include "nfex.mm"
include "nfan.mm"
include "nfeu.mm"
include "nfim.mm"
include "weq.mm"
include "sneq.mm"
include "bnj1318.mm"
include "uneq12d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "bnj1373.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "eubidv.mm"
include "imbi12d.mm"
include "biid.mm"
include "bnj1321.mm"
include "chvar.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "a1i.mm"
include "bnj1366.mm"
include "syl3anc.mm"
include "uniexg.mm"
include "syl.mm"
include "syl5eqel.mm"
include "snex.mm"
include "bnj1149.mm"

theorem bnj1489
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
  assume bnj1489.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1489.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1489.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1489.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1489.5: |- D = { x e. A | -. E. f ta }
  assume bnj1489.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1489.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1489.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1489.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1489.10: |- P = U. H
  assume bnj1489.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1489.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint A y
  disjoint f y
  disjoint x y
  disjoint B f
  disjoint D y
  disjoint G d
  disjoint G f
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint ps y
  disjoint ta y
  assert |- ( ch -> Q e. _V )

  proof
    wch
    cQ
    cP
    vx
    cv
    #
    cZ
    cG
    cfv
    cop
    #
    csn
    #
    cun
    cvv
    bnj1489.12
    wch
    cP
    @2
    wch
    cP
    cH
    cuni
    #
    cvv
    bnj1489.10
    wch
    cH
    cvv
    wcel
    #
    @3
    cvv
    wcel
    wch
    cA
    cR
    @0
    c-bnj14
    #
    cvv
    wcel
    #
    bnjwtam
    vf
    weu
    #
    vy
    @5
    wral
    #
    cH
    bnjwtam
    vy
    @5
    wrex
    vf
    cab
    wceq
    #
    @4
    wch
    @6
    vx
    cA
    wps
    @0
    cD
    wcel
    #
    vy
    cv
    #
    @0
    cR
    wbr
    wn
    #
    vy
    cD
    wral
    #
    @6
    vx
    cA
    wral
    #
    wch
    bnj1489.7
    cA
    cR
    w-bnj15
    #
    cD
    c0
    wne
    #
    @14
    wps
    bnj1489.6
    @15
    cA
    cR
    w-bnj13
    @14
    cA
    cR
    bnj1364
    vx
    cA
    cR
    df-bnj13
    sylib
    bnj832
    bnj835
    wta
    vf
    wex
    wn
    wps
    wch
    @13
    vx
    cA
    cD
    bnj1489.5
    bnj1489.7
    bnj1212
    bnj1294
    wch
    @7
    vy
    @5
    wch
    wps
    @10
    @13
    w3a
    vy
    bnj1489.7
    wps
    @10
    @13
    vy
    wps
    vy
    nfv
    @10
    vy
    nfv
    @12
    vy
    cD
    nfra1
    nf3an
    nfxfr
    wch
    @11
    @5
    wcel
    #
    @7
    wch
    @17
    wa
    @15
    bnjwtam
    vf
    wex
    #
    @7
    wch
    @15
    @17
    wps
    @10
    @13
    @15
    wch
    bnj1489.7
    wps
    @15
    @16
    bnj1489.6
    simplbi
    bnj835
    adantr
    wch
    @18
    vy
    @5
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
    cY
    vd
    bnjwtam
    bnj1489.1
    bnj1489.2
    bnj1489.3
    bnj1489.4
    bnj1489.5
    bnj1489.6
    bnj1489.7
    bnj1489.8
    bnj1388
    r19.21bi
    @15
    vf
    cv
    #
    cC
    wcel
    #
    @19
    cdm
    #
    @0
    csn
    #
    cA
    cR
    @0
    c-bnj18
    #
    cun
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    @26
    vf
    weu
    #
    wi
    @15
    @18
    wa
    #
    @7
    wi
    vx
    vy
    @30
    @7
    vx
    @15
    @18
    vx
    @15
    vx
    nfv
    bnjwtam
    vx
    vf
    bnjwtam
    wta
    vx
    @11
    wsbc
    vx
    bnj1489.8
    wta
    vx
    @11
    nfsbc1v
    nfxfr
    #
    nfex
    nfan
    bnjwtam
    vx
    vf
    @31
    nfeu
    nfim
    vx
    vy
    weq
    #
    @28
    @30
    @29
    @7
    @32
    @27
    @18
    @15
    @32
    @26
    bnjwtam
    vf
    @32
    @26
    @20
    @21
    @11
    csn
    #
    cA
    cR
    @11
    c-bnj18
    #
    cun
    #
    wceq
    #
    wa
    bnjwtam
    @32
    @25
    @36
    @20
    @32
    @24
    @35
    @21
    @32
    @22
    @33
    @23
    @34
    @0
    @11
    sneq
    cA
    cR
    @0
    @11
    bnj1318
    uneq12d
    eqeq2d
    anbi2d
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
    bnj1489.1
    bnj1489.2
    bnj1489.3
    bnj1489.4
    bnj1489.8
    bnj1373
    syl6bbr
    #
    exbidv
    anbi2d
    @32
    @26
    bnjwtam
    vf
    @37
    eubidv
    imbi12d
    @26
    vx
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnj1489.1
    bnj1489.2
    bnj1489.3
    @26
    biid
    bnj1321
    chvar
    syl2anc
    ex
    ralrimi
    @9
    wch
    bnj1489.9
    a1i
    bnjwtam
    @6
    @8
    @9
    w3a
    #
    vy
    vf
    @5
    cH
    @38
    biid
    bnj1366
    syl3anc
    cH
    cvv
    uniexg
    syl
    syl5eqel
    @2
    cvv
    wcel
    wch
    @1
    snex
    a1i
    bnj1149
    syl5eqel
end
