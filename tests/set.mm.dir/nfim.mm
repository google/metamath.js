include "wnf.mm"
include "wi.mm"
include "nfimt2.mm"
include "mp2an.mm"

theorem nfim
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nfim.1: |- F/ x ph
  assume nfim.2: |- F/ x ps


  assert |- F/ x ( ph -> ps )

  proof
    wph
    vx
    wnf
    wps
    vx
    wnf
    wph
    wps
    wi
    vx
    wnf
    nfim.1
    nfim.2
    wph
    wps
    vx
    nfimt2
    mp2an
end
