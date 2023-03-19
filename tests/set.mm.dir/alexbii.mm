include "wal.mm"
include "wex.mm"
include "biimpd.mm"
include "aleximi.mm"
include "biimprd.mm"
include "impbid.mm"

theorem alexbii
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume alexbii.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( A. x ph -> ( E. x ps <-> E. x ch ) )

  proof
    wph
    vx
    wal
    wps
    vx
    wex
    wch
    vx
    wex
    wph
    wps
    wch
    vx
    wph
    wps
    wch
    alexbii.1
    biimpd
    aleximi
    wph
    wch
    wps
    vx
    wph
    wps
    wch
    alexbii.1
    biimprd
    aleximi
    impbid
end
