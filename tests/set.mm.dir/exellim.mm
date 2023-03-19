include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "nfa1.mm"
include "nfv.mm"
include "sp.mm"
include "exlimd.mm"
include "impcom.mm"

theorem exellim
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( ( E. x x e. A /\ A. x ( x e. A -> ph ) ) -> ph )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    vx
    wex
    wph
    @2
    @0
    wph
    vx
    @1
    vx
    nfa1
    wph
    vx
    nfv
    @1
    vx
    sp
    exlimd
    impcom
end
