include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "crab.mm"
include "mptrcl.mm"
include "simp1.mm"
include "cv.mm"
include "wsbc.mm"
include "csb.mm"
include "wa.mm"
include "cvv.mm"
include "wceq.mm"
include "csbeq1.mm"
include "dfsbcq.mm"
include "rabeqbidv.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfcsb1v.mm"
include "nfrab.mm"
include "weq.mm"
include "csbeq1a.mm"
include "sbceq1a.mm"
include "nfsbc.mm"
include "nfv.mm"
include "wb.mm"
include "equcoms.mm"
include "sbccom.mm"
include "syl6rbbr.mm"
include "cbvrab.mm"
include "syl6eqr.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "rabexg.mm"
include "syl.mm"
include "fvmpt3.mm"
include "eleq2d.mm"
include "sbcbidv.mm"
include "elrab.mm"
include "a1i.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "anbi1d.mm"
include "sbc2iegf.mm"
include "pm5.32da.mm"
include "3bitrd.mm"
include "3anass.mm"
include "baibr.mm"
include "pm5.21nii.mm"

theorem elmptrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume elmptrab.f: |- F = ( x e. D |-> { y e. B | ph } )
  assume elmptrab.s1: |- ( ( x = X /\ y = Y ) -> ( ph <-> ps ) )
  assume elmptrab.s2: |- ( x = X -> B = C )
  assume elmptrab.ex: |- ( x e. D -> B e. V )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint V x
  disjoint V y
  disjoint Y x
  disjoint Y y
  disjoint ps x
  disjoint ps y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X w
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint B w
  disjoint B z
  disjoint D z
  disjoint ph w
  disjoint ph z
  disjoint Y w
  assert |- ( Y e. ( F ` X ) <-> ( X e. D /\ Y e. C /\ ps ) )

  proof
    cY
    cX
    cF
    cfv
    #
    wcel
    #
    cX
    cD
    wcel
    #
    @2
    cY
    cC
    wcel
    #
    wps
    w3a
    #
    vx
    cD
    wph
    vy
    cB
    crab
    #
    cF
    cY
    cX
    elmptrab.f
    mptrcl
    @2
    @3
    wps
    simp1
    @2
    @1
    cY
    wph
    vy
    vw
    cv
    #
    wsbc
    #
    vx
    cX
    wsbc
    #
    vw
    vx
    cX
    cB
    csb
    #
    crab
    #
    wcel
    #
    @3
    wps
    wa
    #
    @4
    @2
    @0
    @10
    cY
    vz
    cX
    @7
    vx
    vz
    cv
    #
    wsbc
    #
    vw
    vx
    @13
    cB
    csb
    #
    crab
    #
    @10
    cD
    cF
    cvv
    @13
    cX
    wceq
    @14
    @8
    vw
    @15
    @9
    vx
    @13
    cX
    cB
    csbeq1
    @7
    vx
    @13
    cX
    dfsbcq
    rabeqbidv
    cF
    vx
    cD
    @5
    cmpt
    vz
    cD
    @16
    cmpt
    elmptrab.f
    vx
    vz
    cD
    @5
    @16
    vz
    @5
    nfcv
    @14
    vx
    vw
    @15
    @7
    vx
    @13
    nfsbc1v
    vx
    @13
    cB
    nfcsb1v
    #
    nfrab
    vx
    vz
    weq
    #
    @5
    wph
    vx
    @13
    wsbc
    #
    vy
    @15
    crab
    @16
    @18
    wph
    @19
    vy
    cB
    @15
    vx
    @13
    cB
    csbeq1a
    #
    wph
    vx
    @13
    sbceq1a
    rabeqbidv
    @14
    @19
    vw
    vy
    @15
    vw
    @15
    nfcv
    vy
    @15
    nfcv
    @7
    vy
    vx
    @13
    vy
    @13
    nfcv
    wph
    vy
    @6
    nfsbc1v
    nfsbc
    @19
    vw
    nfv
    vw
    vy
    weq
    @19
    @19
    vy
    @6
    wsbc
    #
    @14
    @19
    @21
    wb
    vy
    vw
    @19
    vy
    @6
    sbceq1a
    equcoms
    wph
    vx
    vy
    @13
    @6
    sbccom
    syl6rbbr
    cbvrab
    syl6eqr
    cbvmpt
    eqtri
    @13
    cD
    wcel
    #
    @15
    cV
    wcel
    #
    @16
    cvv
    wcel
    vx
    cv
    #
    cD
    wcel
    #
    cB
    cV
    wcel
    #
    wi
    @22
    @23
    wi
    vx
    vz
    @22
    @23
    vx
    @22
    vx
    nfv
    vx
    @15
    cV
    @17
    nfel1
    nfim
    @18
    @25
    @22
    @26
    @23
    @24
    @13
    cD
    eleq1
    @18
    cB
    @15
    cV
    @20
    eleq1d
    imbi12d
    elmptrab.ex
    chvar
    @14
    vw
    @15
    cV
    rabexg
    syl
    fvmpt3
    eleq2d
    @2
    @11
    cY
    @9
    wcel
    #
    wph
    vy
    cY
    wsbc
    #
    vx
    cX
    wsbc
    #
    wa
    #
    @3
    @29
    wa
    @12
    @11
    @30
    wb
    @2
    @8
    @29
    vw
    cY
    @9
    @6
    cY
    wceq
    @7
    @28
    vx
    cX
    wph
    vy
    @6
    cY
    dfsbcq
    sbcbidv
    elrab
    a1i
    @2
    @27
    @3
    @29
    @2
    @9
    cC
    cY
    vx
    cX
    cB
    cC
    cD
    @2
    vx
    cC
    nfcvd
    elmptrab.s2
    csbiegf
    eleq2d
    anbi1d
    @2
    @3
    @29
    wps
    wph
    wps
    vx
    vy
    cX
    cY
    cD
    cC
    wps
    vx
    nfv
    wps
    vy
    nfv
    @3
    vx
    nfv
    elmptrab.s1
    sbc2iegf
    pm5.32da
    3bitrd
    @4
    @2
    @12
    @2
    @3
    wps
    3anass
    baibr
    3bitrd
    pm5.21nii
end
