include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnf.mm"
include "wa.mm"
include "nfnae.mm"
include "nfa1.mm"
include "nfan.mm"
include "nfnf1.mm"
include "nfal.mm"
include "simpl.mm"
include "sp.mm"
include "adantl.mm"
include "wl-eudf.mm"

theorem wl-eutf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( -. A. x x = y /\ A. x F/ y ph ) -> ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wa
    wph
    vx
    vy
    @0
    @2
    vx
    vx
    vy
    vx
    nfnae
    @1
    vx
    nfa1
    nfan
    @0
    @2
    vy
    vx
    vy
    vy
    nfnae
    @1
    vy
    vx
    wph
    vy
    nfnf1
    nfal
    nfan
    @0
    @2
    simpl
    @2
    @1
    @0
    @1
    vx
    sp
    adantl
    wl-eudf
end
