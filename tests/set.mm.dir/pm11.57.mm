include "wal.mm"
include "wsb.mm"
include "wa.mm"
include "nfv.mm"
include "nfal.mm"
include "sp.mm"
include "stdpc4.mm"
include "jca.mm"
include "alrimi.mm"
include "axc4i.mm"
include "simpl.mm"
include "sps.mm"
include "alimi.mm"
include "impbii.mm"

theorem pm11.57
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( A. x ph <-> A. x A. y ( ph /\ [ y / x ] ph ) )

  proof
    wph
    vx
    wal
    #
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    vy
    wal
    #
    vx
    wal
    wph
    @3
    vx
    @0
    @2
    vy
    wph
    vy
    vx
    wph
    vy
    nfv
    nfal
    @0
    wph
    @1
    wph
    vx
    sp
    wph
    vx
    vy
    stdpc4
    jca
    alrimi
    axc4i
    @3
    wph
    vx
    @2
    wph
    vy
    wph
    @1
    simpl
    sps
    alimi
    impbii
end
