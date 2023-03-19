include "cv.mm"
include "c-bnj14.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "ciun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "df-iun.mm"
include "bnj1436.mm"
include "simplbiim.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "nfiu1.mm"
include "nfcri.mm"
include "nfan.mm"
include "nf5ri.mm"
include "bnj1521.mm"
include "wex.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "nfe1.mm"
include "nfn.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfne.mm"
include "nfral.mm"
include "simplbi.mm"
include "bnj835.mm"
include "simp2bi.mm"
include "wi.mm"
include "bnj1388.mm"
include "rsp.mm"
include "syl.mm"
include "sylc.mm"
include "bnj596.mm"
include "wceq.mm"
include "bnj1373.mm"
include "adantl.mm"
include "simprbi.mm"
include "rspe.mm"
include "syl2an.mm"
include "abeq2i.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "3bitri.mm"
include "sylanbrc.mm"
include "simp3bi.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "bnj593.mm"
include "df-rex.mm"
include "sylibr.mm"
include "cuni.mm"
include "dmeqi.mm"
include "bnj1317.mm"
include "bnj1400.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfuni.mm"
include "nfdm.mm"
include "nfcrii.mm"
include "bnj1397.mm"
include "sylbir.mm"
include "ex.mm"
include "ssrdv.mm"
include "wss.mm"
include "simpr.mm"
include "eleq2.mm"
include "biimpac.mm"
include "reximi.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "a1i.mm"
include "eqssd.mm"

theorem bnj1398
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let vw: setvar w
  assume bnj1398.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1398.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1398.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1398.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1398.5: |- D = { x e. A | -. E. f ta }
  assume bnj1398.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1398.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1398.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1398.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1398.10: |- P = U. H
  assume bnj1398.11: |- ( th <-> ( ch /\ z e. U_ y e. _pred ( x , A , R ) ( { y } u. _trCl ( y , A , R ) ) ) )
  assume bnj1398.12: |- ( et <-> ( th /\ y e. _pred ( x , A , R ) /\ z e. ( { y } u. _trCl ( y , A , R ) ) ) )

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint C y
  disjoint D y
  disjoint H z
  disjoint P z
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ch z
  disjoint d f
  disjoint d x
  disjoint ps y
  disjoint ta y
  disjoint D w
  disjoint w y
  disjoint H w
  disjoint w z
  disjoint P w
  disjoint f w
  disjoint w x
  assert |- ( ch -> U_ y e. _pred ( x , A , R ) ( { y } u. _trCl ( y , A , R ) ) = dom P )

  proof
    wch
    vy
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    vy
    cv
    #
    csn
    cA
    cR
    @2
    c-bnj18
    cun
    #
    ciun
    #
    cP
    cdm
    #
    wch
    vz
    @4
    @5
    wch
    vz
    cv
    #
    @4
    wcel
    #
    @6
    @5
    wcel
    #
    wch
    @7
    wa
    #
    wth
    @8
    bnj1398.11
    wth
    @8
    vy
    wth
    wet
    @8
    vy
    @6
    @3
    wcel
    #
    wth
    wet
    vy
    @1
    wth
    wch
    @7
    @10
    vy
    @1
    wrex
    #
    bnj1398.11
    @11
    vz
    @4
    vy
    vz
    @1
    @3
    df-iun
    bnj1436
    simplbiim
    bnj1398.12
    wth
    vy
    wth
    @9
    vy
    bnj1398.11
    wch
    @7
    vy
    wch
    wps
    @0
    cD
    wcel
    #
    @2
    @0
    cR
    wbr
    wn
    #
    vy
    cD
    wral
    #
    w3a
    #
    vy
    bnj1398.7
    wps
    @12
    @14
    vy
    wps
    vy
    nfv
    @12
    vy
    nfv
    @13
    vy
    cD
    nfra1
    nf3an
    nfxfr
    vy
    vz
    @4
    vy
    @1
    @3
    nfiu1
    nfcri
    nfan
    nfxfr
    nf5ri
    bnj1521
    wet
    @6
    vf
    cv
    #
    cdm
    #
    wcel
    #
    vf
    cH
    wrex
    #
    @8
    wet
    @16
    cH
    wcel
    #
    @18
    wa
    #
    vf
    wex
    @19
    wet
    wet
    bnjwtam
    wa
    #
    @21
    vf
    wet
    bnjwtam
    vf
    wet
    vf
    wet
    wth
    @2
    @1
    wcel
    #
    @10
    w3a
    vf
    bnj1398.12
    wth
    @23
    @10
    vf
    wth
    @9
    vf
    bnj1398.11
    wch
    @7
    vf
    wch
    @15
    vf
    bnj1398.7
    wps
    @12
    @14
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
    bnj1398.6
    @24
    @25
    vf
    @24
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
    bnj1398.5
    @27
    vf
    vx
    cA
    @26
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
    @28
    nfcri
    @13
    vf
    vy
    cD
    @28
    @13
    vf
    nfv
    nfral
    nf3an
    nfxfr
    @7
    vf
    nfv
    nfan
    nfxfr
    @23
    vf
    nfv
    @10
    vf
    nfv
    nf3an
    nfxfr
    nf5ri
    wet
    wch
    @23
    bnjwtam
    vf
    wex
    #
    wth
    @23
    @10
    wch
    wet
    bnj1398.12
    wth
    wch
    @7
    bnj1398.11
    simplbi
    bnj835
    wet
    wth
    @23
    @10
    bnj1398.12
    simp2bi
    #
    wch
    @29
    vy
    @1
    wral
    @23
    @29
    wi
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
    bnj1398.1
    bnj1398.2
    bnj1398.3
    bnj1398.4
    bnj1398.5
    bnj1398.6
    bnj1398.7
    bnj1398.8
    bnj1388
    @29
    vy
    @1
    rsp
    syl
    sylc
    bnj596
    @22
    @20
    @18
    @22
    @16
    cC
    wcel
    #
    @17
    @3
    wceq
    #
    vy
    @1
    wrex
    #
    @20
    bnjwtam
    @31
    wet
    bnjwtam
    @31
    @32
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
    bnj1398.1
    bnj1398.2
    bnj1398.3
    bnj1398.4
    bnj1398.8
    bnj1373
    #
    simplbi
    adantl
    wet
    @23
    @32
    @33
    bnjwtam
    @30
    bnjwtam
    @31
    @32
    @34
    simprbi
    #
    @32
    vy
    @1
    rspe
    syl2an
    @20
    bnjwtam
    vy
    @1
    wrex
    #
    @31
    @32
    wa
    #
    vy
    @1
    wrex
    @31
    @33
    wa
    @36
    vf
    cH
    bnj1398.9
    abeq2i
    bnjwtam
    @37
    vy
    @1
    @34
    rexbii
    @31
    @32
    vy
    @1
    r19.42v
    3bitri
    #
    sylanbrc
    @22
    @6
    @3
    @17
    wet
    @10
    bnjwtam
    wet
    wth
    @23
    @10
    bnj1398.12
    simp3bi
    adantr
    bnjwtam
    @32
    wet
    @35
    adantl
    eleqtrrd
    jca
    bnj593
    @18
    vf
    cH
    df-rex
    sylibr
    @8
    @6
    vf
    cH
    @17
    ciun
    #
    wcel
    @19
    @5
    @39
    @6
    @5
    cH
    cuni
    #
    cdm
    @39
    cP
    @40
    bnj1398.10
    dmeqi
    vf
    vw
    cH
    @36
    vf
    vw
    cH
    bnj1398.9
    bnj1317
    bnj1400
    eqtri
    eleq2i
    vf
    @6
    cH
    @17
    eliun
    bitri
    #
    sylibr
    bnj593
    vy
    vz
    @5
    vy
    cP
    vy
    cP
    @40
    bnj1398.10
    vy
    cH
    vy
    cH
    @36
    vf
    cab
    bnj1398.9
    @36
    vy
    vf
    bnjwtam
    vy
    @1
    nfre1
    nfab
    nfcxfr
    nfuni
    nfcxfr
    nfdm
    nfcrii
    bnj1397
    sylbir
    ex
    ssrdv
    @5
    @4
    wss
    wch
    vz
    @5
    @4
    @19
    @11
    @8
    @7
    @18
    @11
    vf
    cH
    @21
    @18
    @33
    @11
    @20
    @18
    simpr
    @20
    @33
    @18
    @20
    @31
    @33
    @38
    simprbi
    adantr
    @18
    @33
    wa
    @18
    @32
    wa
    #
    vy
    @1
    wrex
    @11
    @18
    @32
    vy
    @1
    r19.42v
    @42
    @10
    vy
    @1
    @32
    @18
    @10
    @17
    @3
    @6
    eleq2
    biimpac
    reximi
    sylbir
    syl2anc
    rexlimiva
    @41
    vy
    @6
    @1
    @3
    eliun
    3imtr4i
    ssriv
    a1i
    eqssd
end
