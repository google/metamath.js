include "cz.mm"
include "wcel.mm"
include "wsbc.mm"
include "cc0.mm"
include "c0ex.mm"
include "sbcie.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "0z.mm"
include "w3a.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "breq1.mm"
include "3anbi13d.mm"
include "dfsbcq.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "3anbi23d.mm"
include "bibi2d.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "weq.mm"
include "biidd.mm"
include "vex.mm"
include "syl5bbr.mm"
include "ovex.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "bibi12d.mm"
include "vtoclga.mm"
include "3ad2ant2.mm"
include "biimpd.mm"
include "uzind.mm"
include "vtocl2g.mm"
include "3adant3.mm"
include "pm2.43i.mm"
include "mp3an1.mm"
include "wa.mm"
include "mp3an2.mm"
include "bicomd.mm"
include "cr.mm"
include "wo.mm"
include "0re.mm"
include "zre.mm"
include "letric.mm"
include "sylancr.mm"
include "mpjaodan.mm"
include "sbcieg.mm"
include "bitrd.mm"

theorem zindbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vb: setvar b
  assume zindbi.1: |- ( y e. ZZ -> ( ps <-> ch ) )
  assume zindbi.2: |- ( x = y -> ( ph <-> ps ) )
  assume zindbi.3: |- ( x = ( y + 1 ) -> ( ph <-> ch ) )
  assume zindbi.4: |- ( x = 0 -> ( ph <-> th ) )
  assume zindbi.5: |- ( x = A -> ( ph <-> ta ) )

  disjoint ph y
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a y
  disjoint b y
  disjoint A a
  disjoint A b
  disjoint a x
  disjoint b x
  disjoint a ps
  disjoint b ps
  disjoint a ch
  disjoint b ch
  disjoint a th
  disjoint b th
  disjoint a ta
  disjoint b ta
  assert |- ( A e. ZZ -> ( th <-> ta ) )

  proof
    cA
    cz
    wcel
    #
    wth
    wph
    vx
    cA
    wsbc
    #
    wta
    wth
    wph
    vx
    cc0
    wsbc
    #
    @0
    @1
    wph
    wth
    vx
    cc0
    c0ex
    zindbi.4
    sbcie
    @0
    cc0
    cA
    cle
    wbr
    #
    @2
    @1
    wb
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cz
    wcel
    #
    @0
    @3
    @4
    0z
    @6
    @0
    @3
    w3a
    #
    @4
    @6
    @0
    @7
    @4
    wi
    #
    @3
    vy
    cv
    #
    cz
    wcel
    #
    vb
    cv
    #
    cz
    wcel
    #
    @9
    @11
    cle
    wbr
    #
    w3a
    #
    wph
    vx
    @9
    wsbc
    #
    wph
    vx
    @11
    wsbc
    #
    wb
    #
    wi
    #
    @6
    @12
    cc0
    @11
    cle
    wbr
    #
    w3a
    #
    @2
    @16
    wb
    #
    wi
    @8
    vy
    vb
    cc0
    cA
    cz
    cz
    @9
    cc0
    wceq
    #
    @14
    @20
    @17
    @21
    @22
    @10
    @6
    @13
    @19
    @12
    @9
    cc0
    cz
    eleq1
    @9
    cc0
    @11
    cle
    breq1
    3anbi13d
    @22
    @15
    @2
    @16
    wph
    vx
    @9
    cc0
    dfsbcq
    bibi1d
    imbi12d
    @11
    cA
    wceq
    #
    @20
    @7
    @21
    @4
    @23
    @12
    @0
    @19
    @3
    @6
    @11
    cA
    cz
    eleq1
    @11
    cA
    cc0
    cle
    breq2
    3anbi23d
    @23
    @16
    @1
    @2
    wph
    vx
    @11
    cA
    dfsbcq
    bibi2d
    imbi12d
    @15
    wph
    vx
    va
    cv
    #
    wsbc
    #
    wb
    @15
    @15
    wb
    @17
    @15
    wph
    vx
    @11
    c1
    caddc
    co
    #
    wsbc
    #
    wb
    #
    @17
    va
    vb
    @9
    @11
    va
    vy
    weq
    @25
    @15
    @15
    wph
    vx
    @24
    @9
    dfsbcq
    bibi2d
    va
    vb
    weq
    @25
    @16
    @15
    wph
    vx
    @24
    @11
    dfsbcq
    bibi2d
    #
    @24
    @26
    wceq
    @25
    @27
    @15
    wph
    vx
    @24
    @26
    dfsbcq
    bibi2d
    @29
    @10
    @15
    biidd
    @14
    @17
    @28
    @14
    @16
    @27
    @15
    @12
    @10
    @16
    @27
    wb
    #
    @13
    wps
    wch
    wb
    @30
    vy
    @11
    cz
    vy
    vb
    weq
    #
    wps
    @16
    wch
    @27
    wps
    @15
    @31
    @16
    wph
    wps
    vx
    @9
    vy
    vex
    zindbi.2
    sbcie
    wph
    vx
    @9
    @11
    dfsbcq
    syl5bbr
    wch
    wph
    vx
    @9
    c1
    caddc
    co
    #
    wsbc
    @31
    @27
    wph
    wch
    vx
    @32
    @9
    c1
    caddc
    ovex
    zindbi.3
    sbcie
    @31
    wph
    vx
    @32
    @26
    @9
    @11
    c1
    caddc
    oveq1
    sbceq1d
    syl5bbr
    bibi12d
    zindbi.1
    vtoclga
    3ad2ant2
    bibi2d
    biimpd
    uzind
    #
    vtocl2g
    3adant3
    pm2.43i
    mp3an1
    @0
    @5
    wa
    @1
    @2
    @0
    @6
    @5
    @1
    @2
    wb
    #
    0z
    @0
    @6
    @5
    w3a
    #
    @34
    @0
    @6
    @35
    @34
    wi
    #
    @5
    @18
    @0
    @12
    cA
    @11
    cle
    wbr
    #
    w3a
    #
    @1
    @16
    wb
    #
    wi
    @36
    vy
    vb
    cA
    cc0
    cz
    cz
    @9
    cA
    wceq
    #
    @14
    @38
    @17
    @39
    @40
    @10
    @0
    @13
    @37
    @12
    @9
    cA
    cz
    eleq1
    @9
    cA
    @11
    cle
    breq1
    3anbi13d
    @40
    @15
    @1
    @16
    wph
    vx
    @9
    cA
    dfsbcq
    bibi1d
    imbi12d
    @11
    cc0
    wceq
    #
    @38
    @35
    @39
    @34
    @41
    @12
    @6
    @37
    @5
    @0
    @11
    cc0
    cz
    eleq1
    @11
    cc0
    cA
    cle
    breq2
    3anbi23d
    @41
    @16
    @2
    @1
    wph
    vx
    @11
    cc0
    dfsbcq
    bibi2d
    imbi12d
    @33
    vtocl2g
    3adant3
    pm2.43i
    mp3an2
    bicomd
    @0
    cc0
    cr
    wcel
    cA
    cr
    wcel
    @3
    @5
    wo
    0re
    cA
    zre
    cc0
    cA
    letric
    sylancr
    mpjaodan
    syl5bbr
    wph
    wta
    vx
    cA
    cz
    zindbi.5
    sbcieg
    bitrd
end
