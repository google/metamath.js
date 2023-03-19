include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "nfe1.mm"
include "nfbi.mm"
include "ceqex.mm"
include "bibi12d.mm"
include "biid.mm"
include "vtoclg1f.mm"

theorem ceqsexg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ceqsexg.1: |- F/ x ps
  assume ceqsexg.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) )

  proof
    wph
    wph
    wb
    vx
    cv
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    wps
    wb
    vx
    cA
    cV
    @2
    wps
    vx
    @1
    vx
    nfe1
    ceqsexg.1
    nfbi
    @0
    wph
    @2
    wph
    wps
    wph
    vx
    cA
    ceqex
    ceqsexg.2
    bibi12d
    wph
    biid
    vtoclg1f
end
