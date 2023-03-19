include "wi.mm"
include "wal.mm"
include "stdpc5v.mm"
include "wex.mm"
include "ax5e.mm"
include "imim1i.mm"
include "19.38.mm"
include "syl.mm"
include "impbii.mm"

theorem 19.21v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) )

  proof
    wph
    wps
    wi
    vx
    wal
    #
    wph
    wps
    vx
    wal
    #
    wi
    #
    wph
    wps
    vx
    stdpc5v
    @2
    wph
    vx
    wex
    #
    @1
    wi
    @0
    @3
    wph
    @1
    wph
    vx
    ax5e
    imim1i
    wph
    wps
    vx
    19.38
    syl
    impbii
end
