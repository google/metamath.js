include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wsbc.mm"
include "wex.mm"
include "pm14.123a.mm"
include "pm14.123b.mm"
include "bitrd.mm"

theorem pm14.123c
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A w
  disjoint w z
  disjoint A z
  disjoint B w
  disjoint B z
  assert |- ( ( A e. V /\ B e. W ) -> ( A. z A. w ( ph <-> ( z = A /\ w = B ) ) <-> ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\ E. z E. w ph ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    wph
    vz
    cv
    cA
    wceq
    vw
    cv
    cB
    wceq
    wa
    #
    wb
    vw
    wal
    vz
    wal
    wph
    @0
    wi
    vw
    wal
    vz
    wal
    #
    wph
    vw
    cB
    wsbc
    vz
    cA
    wsbc
    wa
    @1
    wph
    vw
    wex
    vz
    wex
    wa
    wph
    vz
    vw
    cA
    cB
    cV
    cW
    pm14.123a
    wph
    vz
    vw
    cA
    cB
    cV
    cW
    pm14.123b
    bitrd
end
