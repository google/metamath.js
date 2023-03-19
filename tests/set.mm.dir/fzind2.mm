include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "elfz2.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "3anass.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "cuz.mm"
include "cfv.mm"
include "eluz2.mm"
include "sylbir.mm"
include "cv.mm"
include "clt.mm"
include "wi.mm"
include "cfzo.mm"
include "elfzo.mm"
include "syl6bir.mm"
include "3coml.mm"
include "3expa.mm"
include "impr.mm"
include "sylan2b.mm"
include "fzind.mm"
include "sylbi.mm"

theorem fzind2
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
  assume fzind2.1: |- ( x = M -> ( ph <-> ps ) )
  assume fzind2.2: |- ( x = y -> ( ph <-> ch ) )
  assume fzind2.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume fzind2.4: |- ( x = K -> ( ph <-> ta ) )
  assume fzind2.5: |- ( N e. ( ZZ>= ` M ) -> ps )
  assume fzind2.6: |- ( y e. ( M ..^ N ) -> ( ch -> th ) )

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
  assert |- ( K e. ( M ... N ) -> ta )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
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
    wa
    #
    wta
    @0
    @1
    @2
    @4
    w3a
    #
    @5
    @6
    wa
    #
    wa
    #
    @8
    cK
    cM
    cN
    elfz2
    @3
    @4
    wa
    #
    @10
    wa
    @3
    @4
    @10
    wa
    #
    wa
    @11
    @8
    @3
    @4
    @10
    anass
    @9
    @12
    @10
    @1
    @2
    @4
    df-3an
    anbi1i
    @7
    @13
    @3
    @4
    @5
    @6
    3anass
    anbi2i
    3bitr4i
    bitri
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cK
    cM
    cN
    fzind2.1
    fzind2.2
    fzind2.3
    fzind2.4
    @1
    @2
    cM
    cN
    cle
    wbr
    w3a
    cN
    cM
    cuz
    cfv
    wcel
    wps
    cM
    cN
    eluz2
    fzind2.5
    sylbir
    vy
    cv
    #
    cz
    wcel
    #
    cM
    @14
    cle
    wbr
    #
    @14
    cN
    clt
    wbr
    #
    w3a
    @3
    @15
    @16
    @17
    wa
    #
    wa
    wch
    wth
    wi
    #
    @15
    @16
    @17
    3anass
    @3
    @15
    @18
    @19
    @1
    @2
    @15
    @18
    @19
    wi
    #
    @15
    @1
    @2
    @20
    @15
    @1
    @2
    w3a
    @18
    @14
    cM
    cN
    cfzo
    co
    wcel
    @19
    @14
    cM
    cN
    elfzo
    fzind2.6
    syl6bir
    3coml
    3expa
    impr
    sylan2b
    fzind
    sylbi
end
