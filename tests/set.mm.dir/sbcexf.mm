include "wex.mm"
include "wsbc.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8e.mm"
include "sbcbii.mm"
include "sbcex2.mm"
include "nfs1v.mm"
include "nfsbc.mm"
include "weq.mm"
include "sbequ12r.mm"
include "sbcbidv.mm"
include "cbvex.mm"
include "3bitri.mm"

theorem sbcexf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume sbcexf.1: |- F/_ y A

  disjoint x y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( [. A / x ]. E. y ph <-> E. y [. A / x ]. ph )

  proof
    wph
    vy
    wex
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
    wex
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
    wex
    wph
    vx
    cA
    wsbc
    #
    vy
    wex
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
    sb8e
    sbcbii
    @1
    vz
    vx
    cA
    sbcex2
    @3
    @4
    vz
    vy
    @1
    vy
    vx
    cA
    sbcexf.1
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
    cbvex
    3bitri
end
