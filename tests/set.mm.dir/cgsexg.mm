include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "biimpa.mm"
include "exlimiv.mm"
include "cv.mm"
include "wceq.mm"
include "elisset.mm"
include "eximi.mm"
include "syl.mm"
include "biimprcd.mm"
include "ancld.mm"
include "eximdv.mm"
include "syl5com.mm"
include "impbid2.mm"

theorem cgsexg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume cgsexg.1: |- ( x = A -> ch )
  assume cgsexg.2: |- ( ch -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ( E. x ( ch /\ ph ) <-> ps ) )

  proof
    cA
    cV
    wcel
    #
    wch
    wph
    wa
    #
    vx
    wex
    #
    wps
    @1
    wps
    vx
    wch
    wph
    wps
    cgsexg.2
    biimpa
    exlimiv
    @0
    wch
    vx
    wex
    #
    wps
    @2
    @0
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    @3
    vx
    cA
    cV
    elisset
    @4
    wch
    vx
    cgsexg.1
    eximi
    syl
    wps
    wch
    @1
    vx
    wps
    wch
    wph
    wch
    wph
    wps
    cgsexg.2
    biimprcd
    ancld
    eximdv
    syl5com
    impbid2
end
