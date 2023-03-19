include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "sp.mm"
include "equs4v.mm"
include "df-sb.mm"
include "sylanbrc.mm"

theorem bj-sb2v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x ( x = y -> ph ) -> [ y / x ] ph )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    @1
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    vy
    wsb
    @1
    vx
    sp
    wph
    vx
    vy
    equs4v
    wph
    vx
    vy
    df-sb
    sylanbrc
end
