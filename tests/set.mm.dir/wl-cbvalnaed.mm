include "weq.mm"
include "wal.mm"
include "wb.mm"
include "wl-dral1d.mm"
include "imp.mm"
include "wn.mm"
include "wa.mm"
include "nfnae.mm"
include "nfan.mm"
include "wl-nfnae1.mm"
include "wnf.mm"
include "wi.mm"
include "adantr.mm"
include "cbv2.mm"
include "pm2.61dan.mm"

theorem wl-cbvalnaed
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume wl-cbvalnaed.1: |- F/ x ph
  assume wl-cbvalnaed.2: |- F/ y ph
  assume wl-cbvalnaed.3: |- ( ph -> ( -. A. x x = y -> F/ y ps ) )
  assume wl-cbvalnaed.4: |- ( ph -> ( -. A. x x = y -> F/ x ch ) )
  assume wl-cbvalnaed.5: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    vx
    vy
    weq
    #
    vx
    wal
    #
    wps
    vx
    wal
    wch
    vy
    wal
    wb
    #
    wph
    @1
    @2
    wph
    wps
    wch
    vx
    vy
    wl-cbvalnaed.1
    wl-cbvalnaed.2
    wl-cbvalnaed.5
    wl-dral1d
    imp
    wph
    @1
    wn
    #
    wa
    wps
    wch
    vx
    vy
    wph
    @3
    vx
    wl-cbvalnaed.1
    vx
    vy
    vx
    nfnae
    nfan
    wph
    @3
    vy
    wl-cbvalnaed.2
    vy
    vx
    wl-nfnae1
    nfan
    wph
    @3
    wps
    vy
    wnf
    wl-cbvalnaed.3
    imp
    wph
    @3
    wch
    vx
    wnf
    wl-cbvalnaed.4
    imp
    wph
    @0
    wps
    wch
    wb
    wi
    @3
    wl-cbvalnaed.5
    adantr
    cbv2
    pm2.61dan
end
