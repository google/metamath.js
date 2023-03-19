include "wcel.mm"
include "wa.mm"
include "wsbc.mm"
include "adantr.mm"
include "wb.mm"
include "bnj1464.mm"
include "adantl.mm"
include "mpbird.mm"
include "spesbcd.mm"

theorem bnj1465
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bnj1465.1: |- ( x = A -> ( ph <-> ps ) )
  assume bnj1465.2: |- ( ps -> A. x ps )
  assume bnj1465.3: |- ( ch -> ps )

  disjoint A x
  disjoint V x
  assert |- ( ( ch /\ A e. V ) -> E. x ph )

  proof
    wch
    cA
    cV
    wcel
    #
    wa
    #
    wph
    vx
    cA
    @1
    wph
    vx
    cA
    wsbc
    #
    wps
    wch
    wps
    @0
    bnj1465.3
    adantr
    @0
    @2
    wps
    wb
    wch
    wph
    wps
    vx
    cA
    cV
    bnj1465.2
    bnj1465.1
    bnj1464
    adantl
    mpbird
    spesbcd
end
