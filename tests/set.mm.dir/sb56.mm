include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nfa1.mm"
include "ax12v2.mm"
include "sp.mm"
include "com12.mm"
include "impbid.mm"
include "equsexv.mm"

theorem sb56
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    vx
    vy
    @1
    vx
    nfa1
    @0
    wph
    @2
    wph
    vx
    vy
    ax12v2
    @2
    @0
    wph
    @1
    vx
    sp
    com12
    impbid
    equsexv
end
