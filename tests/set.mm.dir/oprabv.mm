include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "wbr.mm"
include "w3a.mm"
include "wrel.mm"
include "reloprab.mm"
include "brrelex12.mm"
include "mpan.mm"
include "wi.mm"
include "df-br.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "copab.mm"
include "wsbc.mm"
include "wb.mm"
include "opex.mm"
include "nfcv.mm"
include "nfeq1.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "nfsbc1v.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2exbidv.mm"
include "sbceq1a.mm"
include "anbi2d.mm"
include "opelopabgf.mm"
include "eqcom.mm"
include "vex.mm"
include "opth.mm"
include "bitri.mm"
include "eqvisset.mm"
include "anim12i.mm"
include "sylbi.mm"
include "adantr.mm"
include "exlimivv.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "expcom.mm"
include "sylbid.mm"
include "com12.mm"
include "dfoprab2.mm"
include "eleq2s.mm"
include "adantl.mm"
include "mpcom.mm"

theorem oprabv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w

  disjoint X x
  disjoint X y
  disjoint X z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint X w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint Y w
  disjoint Z w
  disjoint ph w
  assert |- ( <. X , Y >. { <. <. x , y >. , z >. | ph } Z -> ( X e. _V /\ Y e. _V /\ Z e. _V ) )

  proof
    cX
    cY
    cop
    #
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    @0
    cZ
    wph
    vx
    vy
    vz
    coprab
    #
    wbr
    #
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    @2
    w3a
    #
    @4
    wrel
    @5
    @3
    wph
    vx
    vy
    vz
    reloprab
    @0
    cZ
    @4
    brrelex12
    mpan
    @2
    @5
    @8
    wi
    @1
    @5
    @2
    @8
    @5
    @0
    cZ
    cop
    #
    @4
    wcel
    @2
    @8
    wi
    #
    @0
    cZ
    @4
    df-br
    @10
    @9
    vw
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    #
    @4
    @2
    @9
    @18
    wcel
    #
    @8
    @2
    @19
    @0
    @14
    wceq
    #
    wph
    vz
    cZ
    wsbc
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @8
    @1
    @2
    @19
    @24
    wb
    cX
    cY
    opex
    @17
    @20
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    @24
    vw
    vz
    @0
    cZ
    cvv
    cvv
    @26
    vw
    vx
    @25
    vw
    vy
    @20
    wph
    vw
    vw
    @0
    @14
    vw
    @0
    nfcv
    nfeq1
    wph
    vw
    nfv
    nfan
    nfex
    nfex
    @23
    vz
    vx
    @22
    vz
    vy
    @20
    @21
    vz
    vz
    @0
    @14
    vz
    @0
    nfcv
    nfeq1
    wph
    vz
    cZ
    nfsbc1v
    nfan
    nfex
    nfex
    @11
    @0
    wceq
    #
    @16
    @25
    vx
    vy
    @27
    @15
    @20
    wph
    @11
    @0
    @14
    eqeq1
    anbi1d
    2exbidv
    vz
    cv
    cZ
    wceq
    #
    @25
    @22
    vx
    vy
    @28
    wph
    @21
    @20
    wph
    vz
    cZ
    sbceq1a
    anbi2d
    2exbidv
    opelopabgf
    mpan
    @24
    @2
    @8
    @24
    @2
    wa
    @6
    @7
    wa
    #
    @2
    wa
    @8
    @24
    @29
    @2
    @22
    @29
    vx
    vy
    @20
    @29
    @21
    @20
    @12
    cX
    wceq
    #
    @13
    cY
    wceq
    #
    wa
    #
    @29
    @20
    @14
    @0
    wceq
    @32
    @0
    @14
    eqcom
    @12
    @13
    cX
    cY
    vx
    vex
    vy
    vex
    opth
    bitri
    @30
    @6
    @31
    @7
    vx
    cX
    eqvisset
    vy
    cY
    eqvisset
    anim12i
    sylbi
    adantr
    exlimivv
    anim1i
    @6
    @7
    @2
    df-3an
    sylibr
    expcom
    sylbid
    com12
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    eleq2s
    sylbi
    com12
    adantl
    mpcom
end
