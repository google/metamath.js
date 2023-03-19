include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ax12v.mm"
include "equcoms.mm"
include "com12.mm"
include "alrimiv.mm"
include "sp.mm"
include "a2i.mm"
include "alimi.mm"
include "bj-eqs.mm"
include "sylibr.mm"
include "impbii.mm"

theorem bj-sb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( ph <-> A. y ( y = x -> A. x ( x = y -> ph ) ) )

  proof
    wph
    vy
    vx
    weq
    #
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
    wi
    #
    vy
    wal
    #
    wph
    @4
    vy
    @0
    wph
    @3
    wph
    @3
    wi
    vx
    vy
    wph
    vx
    vy
    ax12v
    equcoms
    com12
    alrimiv
    @5
    @0
    wph
    wi
    #
    vy
    wal
    wph
    @4
    @6
    vy
    @0
    @3
    wph
    @3
    wph
    wi
    vx
    vy
    @3
    @1
    wph
    @2
    vx
    sp
    com12
    equcoms
    a2i
    alimi
    wph
    vy
    vx
    bj-eqs
    sylibr
    impbii
end
