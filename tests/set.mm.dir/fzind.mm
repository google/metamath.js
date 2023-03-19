include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "3expib.mm"
include "cr.mm"
include "zre.mm"
include "p1le.mm"
include "3expia.mm"
include "syl2an.mm"
include "imdistanda.mm"
include "imim1d.mm"
include "3ad2ant2.mm"
include "clt.mm"
include "wb.mm"
include "zltp1le.mm"
include "adantlr.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "adantl.mm"
include "3expa.mm"
include "com12.mm"
include "sylbird.mm"
include "ex.mm"
include "com23.mm"
include "expd.mm"
include "3impib.mm"
include "impd.mm"
include "a2d.mm"
include "syld.mm"
include "uzind.mm"
include "expcomd.mm"
include "3expb.mm"
include "3impia.mm"
include "impcom.mm"

theorem fzind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cM: class M
  let cN: class N
  assume fzind.1: |- ( x = M -> ( ph <-> ps ) )
  assume fzind.2: |- ( x = y -> ( ph <-> ch ) )
  assume fzind.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume fzind.4: |- ( x = K -> ( ph <-> ta ) )
  assume fzind.5: |- ( ( M e. ZZ /\ N e. ZZ /\ M <_ N ) -> ps )
  assume fzind.6: |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( y e. ZZ /\ M <_ y /\ y < N ) ) -> ( ch -> th ) )

  disjoint K x
  disjoint M x
  disjoint M y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint ch x
  disjoint ph y
  disjoint ps x
  disjoint ta x
  disjoint th x
  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( K e. ZZ /\ M <_ K /\ K <_ N ) ) -> ta )

  proof
    cK
    cz
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    w3a
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    wta
    @3
    @4
    @5
    wta
    @0
    @1
    @2
    @4
    @5
    wta
    wi
    #
    wi
    @0
    @1
    wa
    #
    @4
    @2
    @7
    @4
    @8
    @2
    @7
    wi
    #
    @4
    @0
    @1
    @9
    @4
    @0
    @1
    w3a
    @5
    @2
    wta
    @5
    vx
    cv
    #
    cN
    cle
    wbr
    #
    wa
    #
    wph
    wi
    @5
    cM
    cN
    cle
    wbr
    #
    wa
    #
    wps
    wi
    @5
    vy
    cv
    #
    cN
    cle
    wbr
    #
    wa
    #
    wch
    wi
    #
    @5
    @15
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    wa
    #
    wth
    wi
    #
    @5
    @2
    wa
    #
    wta
    wi
    vx
    vy
    cM
    cK
    @10
    cM
    wceq
    #
    @12
    @14
    wph
    wps
    @24
    @11
    @13
    @5
    @10
    cM
    cN
    cle
    breq1
    anbi2d
    fzind.1
    imbi12d
    @10
    @15
    wceq
    #
    @12
    @17
    wph
    wch
    @25
    @11
    @16
    @5
    @10
    @15
    cN
    cle
    breq1
    anbi2d
    fzind.2
    imbi12d
    @10
    @19
    wceq
    #
    @12
    @21
    wph
    wth
    @26
    @11
    @20
    @5
    @10
    @19
    cN
    cle
    breq1
    anbi2d
    fzind.3
    imbi12d
    @10
    cK
    wceq
    #
    @12
    @23
    wph
    wta
    @27
    @11
    @2
    @5
    @10
    cK
    cN
    cle
    breq1
    anbi2d
    fzind.4
    imbi12d
    @4
    @5
    @13
    wps
    fzind.5
    3expib
    @4
    @15
    cz
    wcel
    #
    cM
    @15
    cle
    wbr
    #
    w3a
    #
    @18
    @21
    wch
    wi
    #
    @22
    @28
    @4
    @18
    @31
    wi
    @29
    @28
    @21
    @17
    wch
    @28
    @5
    @20
    @16
    @28
    @15
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @20
    @16
    wi
    @5
    @15
    zre
    cN
    zre
    @32
    @33
    @20
    @16
    @15
    cN
    p1le
    3expia
    syl2an
    imdistanda
    imim1d
    3ad2ant2
    @30
    @21
    wch
    wth
    @30
    @5
    @20
    wch
    wth
    wi
    #
    @30
    @20
    @5
    @34
    @4
    @28
    @29
    @20
    @5
    @34
    wi
    #
    wi
    @4
    @28
    @29
    wa
    #
    @20
    @35
    @4
    @5
    @36
    @20
    wa
    #
    @34
    @4
    @5
    @37
    @34
    wi
    @6
    @37
    @36
    @15
    cN
    clt
    wbr
    #
    wa
    #
    @34
    @5
    @39
    @37
    wb
    @4
    @5
    @36
    @38
    @20
    @36
    @5
    @38
    @20
    wb
    #
    @28
    @5
    @40
    @29
    @15
    cN
    zltp1le
    adantlr
    expcom
    pm5.32d
    adantl
    @39
    @6
    @34
    @28
    @29
    @38
    @6
    @34
    wi
    @6
    @28
    @29
    @38
    w3a
    @34
    fzind.6
    expcom
    3expa
    com12
    sylbird
    ex
    com23
    expd
    3impib
    com23
    impd
    a2d
    syld
    uzind
    expcomd
    3expb
    expcom
    com23
    3impia
    impd
    impcom
end
