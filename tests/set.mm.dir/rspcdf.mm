include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wral.mm"
include "ex.mm"
include "alrimi.mm"
include "rspct.mm"
include "sylc.mm"

theorem rspcdf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume rspcdf.1: |- F/ x ph
  assume rspcdf.2: |- F/ x ch
  assume rspcdf.3: |- ( ph -> A e. B )
  assume rspcdf.4: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ph -> ( A. x e. B ps -> ch ) )

  proof
    wph
    vx
    cv
    cA
    wceq
    #
    wps
    wch
    wb
    #
    wi
    #
    vx
    wal
    cA
    cB
    wcel
    wps
    vx
    cB
    wral
    wch
    wi
    wph
    @2
    vx
    rspcdf.1
    wph
    @0
    @1
    rspcdf.4
    ex
    alrimi
    rspcdf.3
    wps
    wch
    vx
    cA
    cB
    rspcdf.2
    rspct
    sylc
end
