include "wn.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "df-sb.mm"
include "exanali.mm"
include "anbi2i.mm"
include "annim.mm"
include "3bitri.mm"
include "dfsb3.mm"
include "xchbinxr.mm"

theorem sbn
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( [ y / x ] -. ph <-> -. [ y / x ] ph )

  proof
    wph
    wn
    #
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    #
    @0
    wi
    #
    @2
    wph
    wi
    vx
    wal
    #
    wi
    #
    wph
    vx
    vy
    wsb
    @1
    @3
    @2
    @0
    wa
    vx
    wex
    #
    wa
    @3
    @4
    wn
    #
    wa
    @5
    wn
    @0
    vx
    vy
    df-sb
    @6
    @7
    @3
    @2
    wph
    vx
    exanali
    anbi2i
    @3
    @4
    annim
    3bitri
    wph
    vx
    vy
    dfsb3
    xchbinxr
end
