include "weq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wo.mm"
include "wn.mm"
include "wsb.mm"
include "df-or.mm"
include "dfsb2.mm"
include "imnan.mm"
include "imbi1i.mm"
include "3bitr4i.mm"

theorem dfsb3
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( [ y / x ] ph <-> ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    wph
    wa
    #
    @0
    wph
    wi
    vx
    wal
    #
    wo
    @1
    wn
    #
    @2
    wi
    wph
    vx
    vy
    wsb
    @0
    wph
    wn
    wi
    #
    @2
    wi
    @1
    @2
    df-or
    wph
    vx
    vy
    dfsb2
    @4
    @3
    @2
    @0
    wph
    imnan
    imbi1i
    3bitr4i
end
