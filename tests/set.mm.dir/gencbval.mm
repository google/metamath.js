include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "gencbvex.mm"
include "exanali.mm"
include "3bitr3i.mm"
include "con4bii.mm"

theorem gencbval
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume gencbval.1: |- A e. _V
  assume gencbval.2: |- ( A = y -> ( ph <-> ps ) )
  assume gencbval.3: |- ( A = y -> ( ch <-> th ) )
  assume gencbval.4: |- ( th <-> E. x ( ch /\ A = y ) )

  disjoint ps x
  disjoint ph y
  disjoint th x
  disjoint ch y
  disjoint A y
  assert |- ( A. x ( ch -> ph ) <-> A. y ( th -> ps ) )

  proof
    wch
    wph
    wi
    vx
    wal
    #
    wth
    wps
    wi
    vy
    wal
    #
    wch
    wph
    wn
    #
    wa
    vx
    wex
    wth
    wps
    wn
    #
    wa
    vy
    wex
    @0
    wn
    @1
    wn
    @2
    @3
    wch
    wth
    vx
    vy
    cA
    gencbval.1
    cA
    vy
    cv
    wceq
    wph
    wps
    gencbval.2
    notbid
    gencbval.3
    gencbval.4
    gencbvex
    wch
    wph
    vx
    exanali
    wth
    wps
    vy
    exanali
    3bitr3i
    con4bii
end
