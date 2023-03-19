include "wnfc.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ex.mm"
include "alrimi.mm"
include "vtoclgft.mm"
include "syl221anc.mm"

theorem vtocldf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtocld.1: |- ( ph -> A e. V )
  assume vtocld.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume vtocld.3: |- ( ph -> ps )
  assume vtocldf.4: |- F/ x ph
  assume vtocldf.5: |- ( ph -> F/_ x A )
  assume vtocldf.6: |- ( ph -> F/ x ch )


  assert |- ( ph -> ch )

  proof
    wph
    vx
    cA
    wnfc
    wch
    vx
    wnf
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
    wps
    vx
    wal
    cA
    cV
    wcel
    wch
    vtocldf.5
    vtocldf.6
    wph
    @2
    vx
    vtocldf.4
    wph
    @0
    @1
    vtocld.2
    ex
    alrimi
    wph
    wps
    vx
    vtocldf.4
    vtocld.3
    alrimi
    vtocld.1
    wps
    wch
    vx
    cA
    cV
    vtoclgft
    syl221anc
end
