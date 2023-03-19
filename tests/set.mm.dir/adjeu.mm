include "chil.mm"
include "wf.mm"
include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cmap.mm"
include "wreu.mm"
include "cvv.mm"
include "wb.mm"
include "ax-hilex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "w3a.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "3anass.mm"
include "syl6bb.mm"
include "exbidv.mm"
include "19.42v.mm"
include "copab.mm"
include "cab.mm"
include "dfadj2.mm"
include "dmeqi.mm"
include "dmopab.mm"
include "eqtri.mm"
include "elab2g.mm"
include "baibd.mm"
include "mpancom.mm"
include "weu.mm"
include "df-reu.mm"
include "elmap.mm"
include "anbi1i.mm"
include "eubii.mm"
include "wmo.mm"
include "adjmo.mm"
include "eu5.mm"
include "mpbiran2.mm"
include "3bitri.mm"
include "syl6bbr.mm"

theorem adjeu
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z

  disjoint u x
  disjoint u y
  disjoint T u
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T : ~H --> ~H -> ( T e. dom adjh <-> E! u e. ( ~H ^m ~H ) A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = ( ( u ` x ) .ih y ) ) )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cado
    cdm
    #
    wcel
    #
    chil
    chil
    vu
    cv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @5
    @3
    cfv
    @6
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    wa
    #
    vu
    wex
    #
    @11
    vu
    chil
    chil
    cmap
    co
    #
    wreu
    #
    cT
    cvv
    wcel
    #
    @0
    @2
    @13
    wb
    @0
    chil
    cvv
    wcel
    #
    @17
    @16
    ax-hilex
    ax-hilex
    chil
    chil
    cT
    cvv
    cvv
    fex2
    mp3an23
    @16
    @2
    @0
    @13
    chil
    chil
    vt
    cv
    #
    wf
    #
    @4
    @5
    @6
    @18
    cfv
    #
    csp
    co
    #
    @9
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vu
    wex
    #
    @0
    @13
    wa
    #
    vt
    cT
    @1
    cvv
    @18
    cT
    wceq
    #
    @25
    @0
    @12
    wa
    #
    vu
    wex
    @26
    @27
    @24
    @28
    vu
    @27
    @24
    @0
    @4
    @11
    w3a
    @28
    @27
    @19
    @0
    @23
    @11
    @4
    chil
    chil
    @18
    cT
    feq1
    @27
    @22
    @10
    vx
    vy
    chil
    chil
    @27
    @21
    @8
    @9
    @27
    @20
    @7
    @5
    csp
    @6
    @18
    cT
    fveq1
    oveq2d
    eqeq1d
    2ralbidv
    3anbi13d
    @0
    @4
    @11
    3anass
    syl6bb
    exbidv
    @0
    @12
    vu
    19.42v
    syl6bb
    @1
    @24
    vt
    vu
    copab
    #
    cdm
    @25
    vt
    cab
    cado
    @29
    vx
    vy
    vu
    vt
    dfadj2
    dmeqi
    @24
    vt
    vu
    dmopab
    eqtri
    elab2g
    baibd
    mpancom
    @15
    @3
    @14
    wcel
    #
    @11
    wa
    #
    vu
    weu
    @12
    vu
    weu
    #
    @13
    @11
    vu
    @14
    df-reu
    @31
    @12
    vu
    @30
    @4
    @11
    chil
    chil
    @3
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    eubii
    @32
    @13
    @12
    vu
    wmo
    vx
    vy
    vu
    cT
    adjmo
    @12
    vu
    eu5
    mpbiran2
    3bitri
    syl6bbr
end
