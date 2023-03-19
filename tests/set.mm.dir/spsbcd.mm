include "wcel.mm"
include "wal.mm"
include "wsbc.mm"
include "spsbc.mm"
include "sylc.mm"

theorem spsbcd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  assume spsbcd.1: |- ( ph -> A e. V )
  assume spsbcd.2: |- ( ph -> A. x ps )


  assert |- ( ph -> [. A / x ]. ps )

  proof
    wph
    cA
    cV
    wcel
    wps
    vx
    wal
    wps
    vx
    cA
    wsbc
    spsbcd.1
    spsbcd.2
    wps
    vx
    cA
    cV
    spsbc
    sylc
end
