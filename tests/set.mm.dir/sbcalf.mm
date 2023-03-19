include "wal.mm"
include "wsbc.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8.mm"
include "sbcbii.mm"
include "sbcal.mm"
include "nfs1v.mm"
include "nfsbc.mm"
include "weq.mm"
include "sbequ12r.mm"
include "sbcbidv.mm"
include "cbval.mm"
include "3bitri.mm"

theorem sbcalf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume sbcalf.1: |- F/_ y A

  disjoint x y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( [. A / x ]. A. y ph <-> A. y [. A / x ]. ph )

  proof
    wph
    vy
    wal
    #
    vx
    cA
    wsbc
    wph
    vy
    vz
    wsb
    #
    vz
    wal
    #
    vx
    cA
    wsbc
    @1
    vx
    cA
    wsbc
    #
    vz
    wal
    wph
    vx
    cA
    wsbc
    #
    vy
    wal
    @0
    @2
    vx
    cA
    wph
    vy
    vz
    wph
    vz
    nfv
    sb8
    sbcbii
    @1
    vz
    vx
    cA
    sbcal
    @3
    @4
    vz
    vy
    @1
    vy
    vx
    cA
    sbcalf.1
    wph
    vy
    vz
    nfs1v
    nfsbc
    @4
    vz
    nfv
    vz
    vy
    weq
    @1
    wph
    vx
    cA
    wph
    vz
    vy
    sbequ12r
    sbcbidv
    cbval
    3bitri
end
