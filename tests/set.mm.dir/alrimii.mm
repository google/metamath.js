include "cv.mm"
include "wsbc.mm"
include "wal.mm"
include "sylibr.mm"
include "alrimi.mm"
include "nfsbc1v.mm"
include "sbceq2a.mm"
include "cbval.mm"
include "sylib.mm"

theorem alrimii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume alrimii.1: |- F/ y ph
  assume alrimii.2: |- ( ph -> ps )
  assume alrimii.3: |- ( [. y / x ]. ch <-> ps )
  assume alrimii.4: |- F/ y ch

  disjoint x y
  assert |- ( ph -> A. x ch )

  proof
    wph
    wch
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    wal
    wch
    vx
    wal
    wph
    @1
    vy
    alrimii.1
    wph
    wps
    @1
    alrimii.2
    alrimii.3
    sylibr
    alrimi
    @1
    wch
    vy
    vx
    wch
    vx
    @0
    nfsbc1v
    alrimii.4
    wch
    vx
    @0
    sbceq2a
    cbval
    sylib
end
