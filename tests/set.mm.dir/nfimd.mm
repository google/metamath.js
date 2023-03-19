include "wnf.mm"
include "wi.mm"
include "nfimt2.mm"
include "syl2anc.mm"

theorem nfimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfimd.1: |- ( ph -> F/ x ps )
  assume nfimd.2: |- ( ph -> F/ x ch )


  assert |- ( ph -> F/ x ( ps -> ch ) )

  proof
    wph
    wps
    vx
    wnf
    wch
    vx
    wnf
    wps
    wch
    wi
    vx
    wnf
    nfimd.1
    nfimd.2
    wps
    wch
    vx
    nfimt2
    syl2anc
end
