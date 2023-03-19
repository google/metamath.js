include "weq.mm"
include "wsb.mm"
include "wb.mm"
include "equid.mm"
include "sbequ12r.mm"
include "ax-mp.mm"

theorem sbid
  param wph: wff ph
  param vx: setvar x


  assert |- ( [ x / x ] ph <-> ph )

  proof
    vx
    vx
    weq
    wph
    vx
    vx
    wsb
    wph
    wb
    vx
    equid
    wph
    vx
    vx
    sbequ12r
    ax-mp
end
