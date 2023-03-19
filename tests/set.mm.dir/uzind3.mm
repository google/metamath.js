include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "breq2.mm"
include "elrab.mm"
include "wi.mm"
include "sylan2br.mm"
include "3impb.mm"
include "uzind.mm"
include "3expb.mm"
include "sylan2b.mm"

theorem uzind3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cM: class M
  let cN: class N
  assume uzind3.1: |- ( j = M -> ( ph <-> ps ) )
  assume uzind3.2: |- ( j = m -> ( ph <-> ch ) )
  assume uzind3.3: |- ( j = ( m + 1 ) -> ( ph <-> th ) )
  assume uzind3.4: |- ( j = N -> ( ph <-> ta ) )
  assume uzind3.5: |- ( M e. ZZ -> ps )
  assume uzind3.6: |- ( ( M e. ZZ /\ m e. { k e. ZZ | M <_ k } ) -> ( ch -> th ) )

  disjoint j k
  disjoint N j
  disjoint N k
  disjoint j ps
  disjoint ch j
  disjoint j th
  disjoint j ta
  disjoint m ph
  disjoint j m
  disjoint M j
  disjoint k m
  disjoint M m
  disjoint M k
  assert |- ( ( M e. ZZ /\ N e. { k e. ZZ | M <_ k } ) -> ta )

  proof
    cN
    cM
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cz
    crab
    #
    wcel
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    wa
    wta
    @1
    @5
    vk
    cN
    cz
    @0
    cN
    cM
    cle
    breq2
    elrab
    @3
    @4
    @5
    wta
    wph
    wps
    wch
    wth
    wta
    vj
    vm
    cM
    cN
    uzind3.1
    uzind3.2
    uzind3.3
    uzind3.4
    uzind3.5
    @3
    vm
    cv
    #
    cz
    wcel
    #
    cM
    @6
    cle
    wbr
    #
    wch
    wth
    wi
    #
    @7
    @8
    wa
    @3
    @6
    @2
    wcel
    @9
    @1
    @8
    vk
    @6
    cz
    @0
    @6
    cM
    cle
    breq2
    elrab
    uzind3.6
    sylan2br
    3impb
    uzind
    3expb
    sylan2b
end
