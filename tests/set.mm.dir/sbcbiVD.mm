include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "idn1.mm"
include "idn2.mm"
include "spsbc.mm"
include "e12.mm"
include "sbcbig.mm"
include "biimpd.mm"
include "in2.mm"
include "in1.mm"

theorem sbcbiVD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( A. x ( ph <-> ps ) -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) )

  proof
    cA
    cB
    wcel
    #
    wph
    wps
    wb
    #
    vx
    wal
    #
    wph
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    wb
    #
    wi
    @0
    @2
    @3
    @0
    @0
    @2
    @1
    vx
    cA
    wsbc
    #
    @3
    @0
    idn1
    #
    @0
    @0
    @2
    @2
    @4
    @5
    @0
    @2
    idn2
    @1
    vx
    cA
    cB
    spsbc
    e12
    @0
    @4
    @3
    wph
    wps
    vx
    cA
    cB
    sbcbig
    biimpd
    e12
    in2
    in1
end
