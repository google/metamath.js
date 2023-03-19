include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "elisset.mm"
include "nfa1.mm"
include "biimpd.mm"
include "a2i.mm"
include "sps.mm"
include "exlimd.mm"
include "syl5com.mm"
include "biimprcd.mm"
include "alrimi.mm"
include "impbid1.mm"

theorem ceqsalgALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ceqsalg.1: |- F/ x ps
  assume ceqsalg.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wi
    #
    vx
    wal
    #
    wps
    @0
    @1
    vx
    wex
    @3
    wps
    vx
    cA
    cV
    elisset
    @3
    @1
    wps
    vx
    @2
    vx
    nfa1
    ceqsalg.1
    @2
    @1
    wps
    wi
    vx
    @1
    wph
    wps
    @1
    wph
    wps
    ceqsalg.2
    biimpd
    a2i
    sps
    exlimd
    syl5com
    wps
    @2
    vx
    ceqsalg.1
    @1
    wph
    wps
    ceqsalg.2
    biimprcd
    alrimi
    impbid1
end
