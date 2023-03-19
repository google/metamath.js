include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "nf5.mm"
include "nfa1.mm"
include "wl-sbhbt.mm"
include "albid.mm"
include "syl5bb.mm"

theorem wl-sbnf1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> ( F/ x ph <-> A. x A. y ( ph -> [ y / x ] ph ) ) )

  proof
    wph
    vx
    wnf
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    wph
    vx
    vy
    wsb
    wi
    vy
    wal
    #
    vx
    wal
    wph
    vx
    nf5
    @2
    @0
    @3
    vx
    @1
    vx
    nfa1
    wph
    vx
    vy
    wl-sbhbt
    albid
    syl5bb
end
