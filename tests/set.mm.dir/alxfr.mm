include "wcel.mm"
include "wal.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "spcgv.mm"
include "com12.mm"
include "alimdv.mm"
include "adantr.mm"
include "nfa1.mm"
include "nfv.mm"
include "sp.mm"
include "syl5ibrcom.mm"
include "exlimd.mm"
include "adantl.mm"
include "impbid.mm"

theorem alxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume alxfr.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( ( A. y A e. B /\ A. x E. y x = A ) -> ( A. x ph <-> A. y ps ) )

  proof
    cA
    cB
    wcel
    #
    vy
    wal
    #
    vx
    cv
    cA
    wceq
    #
    vy
    wex
    #
    vx
    wal
    #
    wa
    wph
    vx
    wal
    #
    wps
    vy
    wal
    #
    @1
    @5
    @6
    wi
    @4
    @5
    @1
    @6
    @5
    @0
    wps
    vy
    @0
    @5
    wps
    wph
    wps
    vx
    cA
    cB
    alxfr.1
    spcgv
    com12
    alimdv
    com12
    adantr
    @4
    @6
    @5
    wi
    @1
    @6
    @4
    @5
    @6
    @3
    wph
    vx
    @6
    @2
    wph
    vy
    wps
    vy
    nfa1
    wph
    vy
    nfv
    @6
    wph
    @2
    wps
    wps
    vy
    sp
    alxfr.1
    syl5ibrcom
    exlimd
    alimdv
    com12
    adantl
    impbid
end
