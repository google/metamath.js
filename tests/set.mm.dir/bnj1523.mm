include "w-bnj15.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "bnj60.mm"
include "bnj835.mm"
include "bnj832.mm"
include "simp2bi.mm"
include "wss.mm"
include "bnj213.mm"
include "a1i.mm"
include "wi.mm"
include "wal.mm"
include "simp3bi.mm"
include "bnj1211.mm"
include "con2b.mm"
include "albii.mm"
include "sylib.mm"
include "bnj1418.mm"
include "imim1i.mm"
include "alimi.mm"
include "syl.mm"
include "bnj1142.mm"
include "cuni.mm"
include "bnj1309.mm"
include "bnj1307.mm"
include "nfcii.mm"
include "nfuni.mm"
include "nfcxfr.mm"
include "nfcrii.mm"
include "bnj1534.mm"
include "bnj1533.mm"
include "bnj1536.mm"
include "opeq2d.mm"
include "fveq2d.mm"
include "bnj1500.mm"
include "bnj1529.mm"
include "ssrab3.mm"
include "bnj1213.mm"
include "bnj1294.mm"
include "ax-5.mm"
include "3eqtr4d.mm"
include "bnj1538.mm"
include "bnj836.mm"
include "neneqd.mm"
include "pm2.65i.mm"
include "nex.mm"
include "c0.mm"
include "wrex.mm"
include "simp1bi.mm"
include "rabeq2i.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "bnj69.mm"
include "syl3anc.mm"
include "bnj1209.mm"
include "mto.mm"
include "simprbi.mm"
include "bnj1542.mm"
include "bnj1525.mm"
include "bnj1521.mm"
include "bnj1541.mm"
include "sylbir.mm"

theorem bnj1523
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let vv: setvar v
  let vw: setvar w
  assume bnj1523.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1523.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1523.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1523.4: |- F = U. C
  assume bnj1523.5: |- ( ph <-> ( R _FrSe A /\ H Fn A /\ A. x e. A ( H ` x ) = ( G ` <. x , ( H |` _pred ( x , A , R ) ) >. ) ) )
  assume bnj1523.6: |- ( ps <-> ( ph /\ F =/= H ) )
  assume bnj1523.7: |- ( ch <-> ( ps /\ x e. A /\ ( F ` x ) =/= ( H ` x ) ) )
  assume bnj1523.8: |- D = { x e. A | ( F ` x ) =/= ( H ` x ) }
  assume bnj1523.9: |- ( th <-> ( ch /\ y e. D /\ A. z e. D -. z R y ) )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y d
  disjoint ch y
  disjoint A v
  disjoint d v
  disjoint f v
  disjoint v x
  disjoint A w
  disjoint d w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C w
  disjoint F w
  disjoint G v
  disjoint G w
  disjoint H v
  disjoint H w
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint R w
  disjoint R v
  assert |- ( ( R _FrSe A /\ H Fn A /\ A. x e. A ( H ` x ) = ( G ` <. x , ( H |` _pred ( x , A , R ) ) >. ) ) -> F = H )

  proof
    cA
    cR
    w-bnj15
    #
    cH
    cA
    wfn
    #
    vx
    cv
    #
    cH
    cfv
    #
    @2
    cH
    cA
    cR
    @2
    c-bnj14
    #
    cres
    cop
    cG
    cfv
    wceq
    vx
    cA
    wral
    #
    w3a
    wph
    cF
    cH
    wceq
    bnj1523.5
    wps
    wph
    cF
    cH
    bnj1523.6
    wps
    wch
    vx
    wex
    wch
    vx
    wch
    wth
    vy
    wex
    wth
    vy
    wth
    vy
    cv
    #
    cF
    cfv
    #
    @6
    cH
    cfv
    #
    wceq
    wth
    @6
    cF
    cA
    cR
    @6
    c-bnj14
    #
    cres
    #
    cop
    #
    cG
    cfv
    #
    @6
    cH
    @9
    cres
    #
    cop
    #
    cG
    cfv
    #
    @7
    @8
    wth
    @11
    @14
    cG
    wth
    @10
    @13
    @6
    wth
    vz
    cA
    @9
    cF
    cH
    wch
    @6
    cD
    wcel
    #
    vz
    cv
    #
    @6
    cR
    wbr
    #
    wn
    #
    vz
    cD
    wral
    #
    cF
    cA
    wfn
    #
    wth
    bnj1523.9
    wps
    @2
    cA
    wcel
    #
    @2
    cF
    cfv
    #
    @3
    wne
    #
    @21
    wch
    bnj1523.7
    wph
    cF
    cH
    wne
    #
    @21
    wps
    bnj1523.6
    @0
    @1
    @5
    @21
    wph
    bnj1523.5
    vx
    cA
    cB
    cC
    cR
    vf
    cF
    cG
    cY
    vd
    bnj1523.1
    bnj1523.2
    bnj1523.3
    bnj1523.4
    bnj60
    bnj835
    bnj832
    #
    bnj835
    bnj835
    wch
    @16
    @20
    @1
    wth
    bnj1523.9
    wps
    @22
    @24
    @1
    wch
    bnj1523.7
    wph
    @25
    @1
    wps
    bnj1523.6
    wph
    @0
    @1
    @5
    bnj1523.5
    simp2bi
    bnj832
    #
    bnj835
    bnj835
    @9
    cA
    wss
    wth
    cA
    cR
    @6
    bnj213
    #
    a1i
    wth
    vz
    cA
    @9
    @17
    cF
    cfv
    cD
    @17
    cH
    cfv
    wth
    @17
    cD
    wcel
    #
    wn
    #
    vz
    @9
    wth
    @18
    @30
    wi
    #
    vz
    wal
    #
    @17
    @9
    wcel
    #
    @30
    wi
    #
    vz
    wal
    wth
    @29
    @19
    wi
    #
    vz
    wal
    @32
    wth
    @19
    vz
    cD
    wth
    wch
    @16
    @20
    bnj1523.9
    simp3bi
    bnj1211
    @35
    @31
    vz
    @29
    @18
    con2b
    albii
    sylib
    @31
    @34
    vz
    @33
    @18
    @30
    vy
    vz
    cA
    cR
    bnj1418
    imim1i
    alimi
    syl
    bnj1142
    @28
    vx
    vz
    vw
    cA
    cD
    cF
    cH
    bnj1523.8
    vx
    vw
    cF
    vx
    cF
    cC
    cuni
    bnj1523.4
    vx
    cC
    vx
    vw
    cC
    vx
    vw
    cB
    cC
    vf
    cG
    cY
    vd
    bnj1523.3
    vx
    vw
    cA
    cB
    cR
    vd
    bnj1523.1
    bnj1309
    bnj1307
    nfcii
    nfuni
    nfcxfr
    nfcrii
    #
    bnj1534
    bnj1533
    bnj1536
    opeq2d
    fveq2d
    wth
    @7
    @12
    wceq
    #
    vy
    cA
    wch
    @16
    @20
    @37
    vy
    cA
    wral
    wth
    bnj1523.9
    wch
    vx
    vy
    vw
    cA
    cR
    cF
    cG
    wps
    @22
    @24
    @23
    @2
    cF
    @4
    cres
    cop
    cG
    cfv
    wceq
    vx
    cA
    wral
    #
    wch
    bnj1523.7
    wph
    @25
    @38
    wps
    bnj1523.6
    @0
    @1
    @5
    @38
    wph
    bnj1523.5
    vx
    cA
    cB
    cC
    cR
    vf
    cF
    cG
    cY
    vd
    bnj1523.1
    bnj1523.2
    bnj1523.3
    bnj1523.4
    bnj1500
    bnj835
    bnj832
    bnj835
    @36
    bnj1529
    bnj835
    wth
    vy
    cD
    cA
    @24
    vx
    cA
    cD
    bnj1523.8
    ssrab3
    #
    wth
    wch
    @16
    @20
    bnj1523.9
    simp2bi
    bnj1213
    #
    bnj1294
    wth
    @8
    @15
    wceq
    #
    vy
    cA
    wch
    @16
    @20
    @41
    vy
    cA
    wral
    wth
    bnj1523.9
    wch
    vx
    vy
    vv
    cA
    cR
    cH
    cG
    wps
    @22
    @24
    @5
    wch
    bnj1523.7
    wph
    @25
    @5
    wps
    bnj1523.6
    wph
    @0
    @1
    @5
    bnj1523.5
    simp3bi
    bnj832
    bnj835
    vv
    cv
    cH
    wcel
    vx
    ax-5
    bnj1529
    bnj835
    @40
    bnj1294
    3eqtr4d
    wth
    @7
    @8
    wch
    @16
    @20
    @7
    @8
    wne
    #
    wth
    bnj1523.9
    @42
    vy
    cD
    cA
    vx
    vy
    vw
    cA
    cD
    cF
    cH
    bnj1523.8
    @36
    bnj1534
    bnj1538
    bnj836
    neneqd
    pm2.65i
    nex
    @20
    wch
    wth
    vy
    cD
    wch
    @0
    cD
    cA
    wss
    #
    cD
    c0
    wne
    #
    @20
    vy
    cD
    wrex
    wps
    @22
    @24
    @0
    wch
    bnj1523.7
    wph
    @25
    @0
    wps
    bnj1523.6
    wph
    @0
    @1
    @5
    bnj1523.5
    simp1bi
    bnj832
    bnj835
    @43
    wch
    @39
    a1i
    wch
    @2
    cD
    wcel
    #
    @44
    wch
    @22
    @24
    @45
    wch
    wps
    @22
    @24
    bnj1523.7
    simp2bi
    wch
    wps
    @22
    @24
    bnj1523.7
    simp3bi
    @24
    vx
    cD
    cA
    bnj1523.8
    rabeq2i
    sylanbrc
    cD
    @2
    ne0i
    syl
    vy
    vz
    cA
    cD
    cR
    bnj69
    syl3anc
    bnj1523.9
    bnj1209
    mto
    nex
    @24
    wps
    wch
    vx
    cA
    wps
    vx
    vw
    cA
    cF
    cH
    @26
    @27
    wps
    wph
    @25
    bnj1523.6
    simprbi
    @36
    bnj1542
    bnj1523.7
    wph
    wps
    vx
    cA
    cB
    cC
    cR
    vf
    cF
    cG
    cH
    cY
    vd
    bnj1523.1
    bnj1523.2
    bnj1523.3
    bnj1523.4
    bnj1523.5
    bnj1523.6
    bnj1525
    bnj1521
    mto
    bnj1541
    sylbir
end
