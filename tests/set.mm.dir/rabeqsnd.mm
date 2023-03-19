include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "crab.mm"
include "csn.mm"
include "wi.mm"
include "expl.mm"
include "alrimiv.mm"
include "jca.mm"
include "a1d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "sylibr.mm"
include "albiim.mm"
include "rabeqsn.mm"

theorem rabeqsnd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqsnd.0: |- ( x = B -> ( ps <-> ch ) )
  assume rabeqsnd.1: |- ( ph -> B e. A )
  assume rabeqsnd.2: |- ( ph -> ch )
  assume rabeqsnd.3: |- ( ( ( ph /\ x e. A ) /\ ps ) -> x = B )

  disjoint B x
  disjoint ph x
  assert |- ( ph -> { x e. A | ps } = { B } )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    @0
    cB
    wceq
    #
    wb
    vx
    wal
    #
    wps
    vx
    cA
    crab
    cB
    csn
    wceq
    wph
    @2
    @3
    wi
    #
    vx
    wal
    #
    @3
    @2
    wi
    #
    vx
    wal
    #
    wa
    @4
    wph
    @6
    @8
    wph
    @5
    vx
    wph
    @1
    wps
    @3
    rabeqsnd.3
    expl
    alrimiv
    wph
    @3
    cB
    cA
    wcel
    #
    wch
    wa
    #
    wi
    #
    vx
    wal
    @8
    wph
    @11
    vx
    wph
    @10
    @3
    wph
    @9
    wch
    rabeqsnd.1
    rabeqsnd.2
    jca
    a1d
    alrimiv
    @7
    @11
    vx
    @3
    @2
    @10
    @3
    @1
    @9
    wps
    wch
    @0
    cB
    cA
    eleq1
    rabeqsnd.0
    anbi12d
    pm5.74i
    albii
    sylibr
    jca
    @2
    @3
    vx
    albiim
    sylibr
    wps
    vx
    cA
    cB
    rabeqsn
    sylibr
end
