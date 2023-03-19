include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "sbcco.mm"
include "ax-5.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "nfcii.mm"
include "nfeq2.mm"
include "nfsbc1v.mm"
include "nf5i.mm"
include "nfbi.mm"
include "nfim.mm"
include "nf5ri.mm"
include "weq.mm"
include "ax6ev.mm"
include "eqeq1.mm"
include "syl6bir.mm"
include "sbceq1a.mm"
include "bibi1d.mm"
include "sylibd.mm"
include "bnj101.mm"
include "bnj1131.mm"
include "bnj1464.mm"
include "syl5bbr.mm"

theorem bnj1468
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  assume bnj1468.1: |- ( ps -> A. x ps )
  assume bnj1468.2: |- ( x = A -> ( ph <-> ps ) )
  assume bnj1468.3: |- ( y e. A -> A. x y e. A )

  disjoint A y
  disjoint V y
  disjoint ph y
  disjoint ps y
  disjoint x y
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ps ) )

  proof
    wph
    vx
    cA
    wsbc
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    cA
    wsbc
    cA
    cV
    wcel
    wps
    wph
    vx
    vy
    cA
    sbcco
    @1
    wps
    vy
    cA
    cV
    wps
    vy
    ax-5
    @0
    cA
    wceq
    #
    @1
    wps
    wb
    #
    wi
    #
    vx
    @4
    vx
    @2
    @3
    vx
    vx
    @0
    cA
    vx
    vy
    cA
    bnj1468.3
    nfcii
    nfeq2
    @1
    wps
    vx
    wph
    vx
    @0
    nfsbc1v
    wps
    vx
    bnj1468.1
    nf5i
    nfbi
    nfim
    nf5ri
    vx
    vy
    weq
    #
    @4
    vx
    vx
    vy
    ax6ev
    @5
    @2
    wph
    wps
    wb
    #
    @3
    @5
    @2
    vx
    cv
    #
    cA
    wceq
    @6
    @7
    @0
    cA
    eqeq1
    bnj1468.2
    syl6bir
    @5
    wph
    @1
    wps
    wph
    vx
    @0
    sbceq1a
    bibi1d
    sylibd
    bnj101
    bnj1131
    bnj1464
    syl5bbr
end
