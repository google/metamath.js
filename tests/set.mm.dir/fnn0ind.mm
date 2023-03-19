include "cn0.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "cc0.mm"
include "wi.mm"
include "elnn0z.mm"
include "w3a.mm"
include "nn0z.mm"
include "0z.mm"
include "sylbir.mm"
include "3adant1.mm"
include "cv.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "0re.mm"
include "lelttr.mm"
include "ltle.mm"
include "3adant2.mm"
include "syld.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "ex.mm"
include "com23.mm"
include "3impib.mm"
include "impcom.mm"
include "anbi1i.mm"
include "3expb.mm"
include "syl2anbr.mm"
include "expcom.mm"
include "3impa.mm"
include "expd.mm"
include "mpd.mm"
include "adantll.mm"
include "fzind.mm"
include "mpanl1.mm"
include "syl5.mm"
include "3expa.mm"
include "sylanb.mm"
include "3impb.mm"

theorem fnn0ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cN: class N
  assume fnn0ind.1: |- ( x = 0 -> ( ph <-> ps ) )
  assume fnn0ind.2: |- ( x = y -> ( ph <-> ch ) )
  assume fnn0ind.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume fnn0ind.4: |- ( x = K -> ( ph <-> ta ) )
  assume fnn0ind.5: |- ( N e. NN0 -> ps )
  assume fnn0ind.6: |- ( ( N e. NN0 /\ y e. NN0 /\ y < N ) -> ( ch -> th ) )

  disjoint K x
  disjoint N x
  disjoint N y
  disjoint x y
  disjoint ch x
  disjoint ph y
  disjoint ps x
  disjoint ta x
  disjoint th x
  assert |- ( ( N e. NN0 /\ K e. NN0 /\ K <_ N ) -> ta )

  proof
    cN
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    wta
    @1
    @2
    wa
    @0
    wta
    @1
    cK
    cz
    wcel
    #
    cc0
    cK
    cle
    wbr
    #
    wa
    @2
    @0
    wta
    wi
    #
    cK
    elnn0z
    @3
    @4
    @2
    @5
    @0
    cN
    cz
    wcel
    #
    @3
    @4
    @2
    w3a
    #
    wta
    cN
    nn0z
    @6
    @7
    wta
    cc0
    cz
    wcel
    #
    @6
    @7
    wta
    0z
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cK
    cc0
    cN
    fnn0ind.1
    fnn0ind.2
    fnn0ind.3
    fnn0ind.4
    @6
    cc0
    cN
    cle
    wbr
    #
    wps
    @8
    @6
    @9
    wa
    #
    @0
    wps
    cN
    elnn0z
    #
    fnn0ind.5
    sylbir
    3adant1
    @6
    vy
    cv
    #
    cz
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @12
    cN
    clt
    wbr
    #
    w3a
    #
    wch
    wth
    wi
    #
    @8
    @6
    @16
    wa
    @9
    @17
    @16
    @6
    @9
    @13
    @14
    @15
    @6
    @9
    wi
    @13
    @6
    @14
    @15
    wa
    #
    @9
    @13
    @6
    @18
    @9
    wi
    #
    @13
    @12
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @19
    @6
    @12
    zre
    cN
    zre
    cc0
    cr
    wcel
    #
    @20
    @21
    @19
    0re
    @22
    @20
    @21
    w3a
    @18
    cc0
    cN
    clt
    wbr
    #
    @9
    cc0
    @12
    cN
    lelttr
    @22
    @21
    @23
    @9
    wi
    @20
    cc0
    cN
    ltle
    3adant2
    syld
    mp3an1
    syl2an
    ex
    com23
    3impib
    impcom
    @16
    @6
    @9
    @17
    wi
    @16
    @6
    @9
    @17
    @13
    @14
    @15
    @10
    @17
    wi
    @10
    @13
    @14
    wa
    #
    @15
    wa
    #
    @17
    @10
    @0
    @12
    cn0
    wcel
    #
    @15
    wa
    @17
    @25
    @11
    @26
    @24
    @15
    @12
    elnn0z
    anbi1i
    @0
    @26
    @15
    @17
    fnn0ind.6
    3expb
    syl2anbr
    expcom
    3impa
    expd
    impcom
    mpd
    adantll
    fzind
    mpanl1
    expcom
    syl5
    3expa
    sylanb
    impcom
    3impb
end
