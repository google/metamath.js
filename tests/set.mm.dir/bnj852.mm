include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wfn.mm"
include "w3a.mm"
include "weu.mm"
include "wral.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "adantl.mm"
include "ancri.mm"
include "bnj534.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "biimpar.mm"
include "wi.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "biid.mm"
include "com.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "omex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "zfregfr.mm"
include "bnj157.mm"
include "c1o.mm"
include "bnj153.mm"
include "bnj601.mm"
include "pm2.61ine.mm"
include "ex.mm"
include "mprg.mm"
include "r19.21v.mm"
include "mpbi.mm"
include "syl.mm"
include "wb.mm"
include "bnj602.mm"
include "eqeq2d.mm"
include "syl6bbr.mm"
include "3anbi2d.mm"
include "eubidv.mm"
include "ralbidv.mm"
include "adantr.mm"
include "mpbid.mm"
include "bnj593.mm"
include "bnj937.mm"

theorem bnj852
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  let vz: setvar z
  assume bnj852.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj852.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj852.3: |- D = ( _om \ { (/) } )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X n
  disjoint A x
  disjoint A z
  disjoint f x
  disjoint f z
  disjoint i x
  disjoint i z
  disjoint n x
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D x
  disjoint D z
  disjoint R x
  disjoint R z
  disjoint X x
  disjoint ph x
  disjoint ps x
  disjoint ps z
  assert |- ( ( R _FrSe A /\ X e. A ) -> A. n e. D E! f ( f Fn n /\ ph /\ ps ) )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vf
    weu
    #
    vn
    cD
    wral
    #
    vx
    @2
    vx
    cv
    #
    cX
    wceq
    #
    @2
    wa
    #
    @8
    vx
    @10
    @2
    @2
    vx
    @2
    @10
    vx
    wex
    #
    @1
    @12
    @0
    vx
    cX
    cA
    elisset
    adantl
    ancri
    bnj534
    @11
    @5
    c0
    @3
    cfv
    #
    cA
    cR
    @9
    c-bnj14
    #
    wceq
    #
    wps
    w3a
    #
    vf
    weu
    #
    vn
    cD
    wral
    #
    @8
    @11
    @0
    @9
    cA
    wcel
    #
    wa
    #
    @18
    @10
    @20
    @2
    @10
    @19
    @1
    @0
    @9
    cX
    cA
    eleq1
    anbi2d
    biimpar
    @20
    @17
    wi
    #
    vn
    cD
    wral
    #
    @20
    @18
    wi
    vz
    cv
    #
    @4
    cep
    wbr
    @21
    vn
    @23
    wsbc
    wi
    vz
    cD
    wral
    #
    @21
    wi
    @22
    vn
    cD
    @21
    @24
    vn
    vz
    cD
    cep
    @24
    biid
    #
    cD
    com
    c0
    csn
    #
    cdif
    #
    cvv
    bnj852.3
    com
    cvv
    wcel
    @27
    cvv
    wcel
    omex
    com
    @26
    cvv
    difexg
    ax-mp
    eqeltri
    cD
    zfregfr
    bnj157
    @4
    cD
    wcel
    #
    @24
    @21
    @28
    @24
    wa
    @21
    wi
    @4
    c1o
    @15
    wps
    @21
    @24
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vz
    vn
    @15
    biid
    #
    bnj852.2
    bnj852.3
    @21
    biid
    #
    @25
    bnj153
    @15
    wps
    @21
    @24
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vz
    vn
    @29
    bnj852.2
    bnj852.3
    @30
    @25
    bnj601
    pm2.61ine
    ex
    mprg
    @20
    @17
    vn
    cD
    r19.21v
    mpbi
    syl
    @10
    @18
    @8
    wb
    @2
    @10
    @17
    @7
    vn
    cD
    @10
    @16
    @6
    vf
    @10
    @15
    wph
    @5
    wps
    @10
    @15
    @13
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    wph
    @10
    @14
    @31
    @13
    cA
    cR
    @9
    cX
    bnj602
    eqeq2d
    bnj852.1
    syl6bbr
    3anbi2d
    eubidv
    ralbidv
    adantr
    mpbid
    bnj593
    bnj937
end
