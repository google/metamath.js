include "wex.mm"
include "wn.mm"
include "wo.mm"
include "nfe1.mm"
include "nfn.mm"
include "wb.mm"
include "19.8a.mm"
include "con3i.mm"
include "biorf.mm"
include "bicomd.mm"
include "syl.mm"
include "eubid.mm"

theorem euor2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) )

  proof
    wph
    vx
    wex
    #
    wn
    #
    wph
    wps
    wo
    #
    wps
    vx
    @0
    vx
    wph
    vx
    nfe1
    nfn
    @1
    wph
    wn
    #
    @2
    wps
    wb
    wph
    @0
    wph
    vx
    19.8a
    con3i
    @3
    wps
    @2
    wph
    wps
    biorf
    bicomd
    syl
    eubid
end
