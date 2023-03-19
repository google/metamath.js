include "wsb.mm"
include "wb.mm"
include "weq.mm"
include "equsb2.mm"
include "sbequ12r.mm"
include "sbimi.mm"
include "ax-mp.mm"
include "sbbi.mm"
include "mpbi.mm"

theorem bj-sbidmOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph )

  proof
    wph
    vx
    vy
    wsb
    #
    wph
    wb
    #
    vx
    vy
    wsb
    #
    @0
    vx
    vy
    wsb
    @0
    wb
    vy
    vx
    weq
    #
    vx
    vy
    wsb
    @2
    vx
    vy
    equsb2
    @3
    @1
    vx
    vy
    wph
    vy
    vx
    sbequ12r
    sbimi
    ax-mp
    @0
    wph
    vx
    vy
    sbbi
    mpbi
end
