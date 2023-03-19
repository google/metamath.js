include "wal.mm"
include "wsbc.mm"
include "sbcalf.mm"
include "albii.mm"
include "bitri.mm"

theorem sbcalfi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume sbcalfi.1: |- F/_ y A
  assume sbcalfi.2: |- ( [. A / x ]. ph <-> ps )

  disjoint x y
  assert |- ( [. A / x ]. A. y ph <-> A. y ps )

  proof
    wph
    vy
    wal
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    wal
    wps
    vy
    wal
    wph
    vx
    vy
    cA
    sbcalfi.1
    sbcalf
    @0
    wps
    vy
    sbcalfi.2
    albii
    bitri
end
