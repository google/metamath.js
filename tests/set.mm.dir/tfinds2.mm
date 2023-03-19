include "wi.mm"
include "c0.mm"
include "wsbc.mm"
include "0ex.mm"
include "cv.mm"
include "wceq.mm"
include "imbi2d.mm"
include "sbcie.mm"
include "mpbir.mm"
include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cvv.mm"
include "vex.mm"
include "a2d.mm"
include "sbcth.mm"
include "ax-mp.mm"
include "wb.mm"
include "sbcimg.mm"
include "mpbi.mm"
include "sbcel1v.mm"
include "3imtr3i.mm"
include "weq.mm"
include "bicomd.mm"
include "equcoms.mm"
include "sucex.mm"
include "sbcbii.mm"
include "suceq.mm"
include "sbcco2.mm"
include "bitr3i.mm"
include "3imtr3g.mm"
include "wral.mm"
include "wlim.mm"
include "wsb.mm"
include "sbsbc.mm"
include "sbralie.mm"
include "r19.21v.mm"
include "syl5bi.mm"
include "limeq.mm"
include "syl5bir.mm"
include "tfindes.mm"

theorem tfinds2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  assume tfinds2.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume tfinds2.2: |- ( x = y -> ( ph <-> ch ) )
  assume tfinds2.3: |- ( x = suc y -> ( ph <-> th ) )
  assume tfinds2.4: |- ( ta -> ps )
  assume tfinds2.5: |- ( y e. On -> ( ta -> ( ch -> th ) ) )
  assume tfinds2.6: |- ( Lim x -> ( ta -> ( A. y e. x ch -> ph ) ) )

  disjoint x y
  disjoint ta x
  disjoint ta y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ph y
  assert |- ( x e. On -> ( ta -> ph ) )

  proof
    wta
    wph
    wi
    #
    vx
    vy
    @0
    vx
    c0
    wsbc
    wta
    wps
    wi
    #
    tfinds2.4
    @0
    @1
    vx
    c0
    0ex
    vx
    cv
    #
    c0
    wceq
    wph
    wps
    wta
    tfinds2.1
    imbi2d
    sbcie
    mpbir
    @2
    con0
    wcel
    #
    wta
    wch
    wi
    #
    vy
    @2
    wsbc
    #
    wta
    wth
    wi
    #
    vy
    @2
    wsbc
    #
    @0
    @0
    vx
    @2
    csuc
    #
    wsbc
    #
    vy
    cv
    #
    con0
    wcel
    #
    vy
    @2
    wsbc
    #
    @4
    @6
    wi
    #
    vy
    @2
    wsbc
    #
    @3
    @5
    @7
    wi
    #
    @11
    @13
    wi
    #
    vy
    @2
    wsbc
    #
    @12
    @14
    wi
    #
    @2
    cvv
    wcel
    #
    @17
    vx
    vex
    #
    @16
    vy
    @2
    cvv
    @11
    wta
    wch
    wth
    tfinds2.5
    a2d
    sbcth
    ax-mp
    @19
    @17
    @18
    wb
    @20
    @11
    @13
    vy
    @2
    cvv
    sbcimg
    ax-mp
    mpbi
    vy
    @2
    con0
    sbcel1v
    @19
    @14
    @15
    wb
    @20
    @4
    @6
    vy
    @2
    cvv
    sbcimg
    ax-mp
    3imtr3i
    @4
    @0
    vy
    @2
    @20
    vy
    vx
    weq
    wch
    wph
    wta
    wch
    wph
    wb
    vx
    vy
    vx
    vy
    weq
    wph
    wch
    tfinds2.2
    bicomd
    equcoms
    imbi2d
    #
    sbcie
    @7
    @0
    vx
    @10
    csuc
    #
    wsbc
    #
    vy
    @2
    wsbc
    @9
    @23
    @6
    vy
    @2
    @0
    @6
    vx
    @22
    @10
    vy
    vex
    #
    sucex
    @2
    @22
    wceq
    wph
    wth
    wta
    tfinds2.3
    imbi2d
    sbcie
    sbcbii
    @0
    vx
    vy
    @8
    @22
    @2
    @10
    suceq
    sbcco2
    bitr3i
    3imtr3g
    @0
    vx
    @10
    wral
    #
    @4
    vy
    @2
    wral
    #
    vx
    @10
    wsbc
    #
    @10
    wlim
    #
    @0
    vx
    @10
    wsbc
    #
    @27
    @26
    vx
    vy
    wsb
    @25
    @26
    vx
    vy
    sbsbc
    @4
    @0
    vy
    vx
    @21
    sbralie
    bitr3i
    @2
    wlim
    #
    vx
    @10
    wsbc
    #
    @26
    @0
    wi
    #
    vx
    @10
    wsbc
    #
    @28
    @27
    @29
    wi
    #
    @30
    @32
    wi
    #
    vx
    @10
    wsbc
    #
    @31
    @33
    wi
    #
    @10
    cvv
    wcel
    #
    @36
    @24
    @35
    vx
    @10
    cvv
    @26
    wta
    wch
    vy
    @2
    wral
    #
    wi
    @30
    @0
    wta
    wch
    vy
    @2
    r19.21v
    @30
    wta
    @39
    wph
    tfinds2.6
    a2d
    syl5bi
    sbcth
    ax-mp
    @38
    @36
    @37
    wb
    @24
    @30
    @32
    vx
    @10
    cvv
    sbcimg
    ax-mp
    mpbi
    @30
    @28
    vx
    @10
    @24
    @2
    @10
    limeq
    sbcie
    @38
    @33
    @34
    wb
    @24
    @26
    @0
    vx
    @10
    cvv
    sbcimg
    ax-mp
    3imtr3i
    syl5bir
    tfindes
end
