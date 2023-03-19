include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "eluzle.mm"
include "breq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "eluz2.mm"
include "biimpri.mm"
include "3expb.mm"
include "sylan2b.mm"
include "syl.mm"
include "uzind3.mm"
include "syl2anc.mm"

theorem uzind4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume uzind4.1: |- ( j = M -> ( ph <-> ps ) )
  assume uzind4.2: |- ( j = k -> ( ph <-> ch ) )
  assume uzind4.3: |- ( j = ( k + 1 ) -> ( ph <-> th ) )
  assume uzind4.4: |- ( j = N -> ( ph <-> ta ) )
  assume uzind4.5: |- ( M e. ZZ -> ps )
  assume uzind4.6: |- ( k e. ( ZZ>= ` M ) -> ( ch -> th ) )

  disjoint N j
  disjoint j ps
  disjoint ch j
  disjoint j th
  disjoint j ta
  disjoint k ph
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint j m
  disjoint N m
  disjoint k m
  disjoint M m
  assert |- ( N e. ( ZZ>= ` M ) -> ta )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cM
    vm
    cv
    #
    cle
    wbr
    #
    vm
    cz
    crab
    #
    wcel
    #
    wta
    cM
    cN
    eluzel2
    @1
    cN
    cz
    wcel
    cM
    cN
    cle
    wbr
    #
    @6
    cM
    cN
    eluzelz
    cM
    cN
    eluzle
    @4
    @7
    vm
    cN
    cz
    @3
    cN
    cM
    cle
    breq2
    elrab
    sylanbrc
    wph
    wps
    wch
    wth
    wta
    vj
    vm
    vk
    cM
    cN
    uzind4.1
    uzind4.2
    uzind4.3
    uzind4.4
    uzind4.5
    @2
    vk
    cv
    #
    @5
    wcel
    #
    wa
    @8
    @0
    wcel
    #
    wch
    wth
    wi
    @9
    @2
    @8
    cz
    wcel
    #
    cM
    @8
    cle
    wbr
    #
    wa
    @10
    @4
    @12
    vm
    @8
    cz
    @3
    @8
    cM
    cle
    breq2
    elrab
    @2
    @11
    @12
    @10
    @10
    @2
    @11
    @12
    w3a
    cM
    @8
    eluz2
    biimpri
    3expb
    sylan2b
    uzind4.6
    syl
    uzind3
    syl2anc
end
