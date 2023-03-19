include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "dfsbcq.mm"
include "csbeq1.mm"
include "sbceq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "csbeq1a.mm"
include "adantl.mm"
include "nfnf1.mm"
include "nfal.mm"
include "nfa1.mm"
include "wnfc.mm"
include "nfcsb1v.mm"
include "sp.mm"
include "nfsbcd.mm"
include "sbciedf.mm"
include "vtoclg.mm"
include "imp.mm"

theorem sbcnestgf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. V /\ A. y F/ x ph ) -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    wnf
    #
    vy
    wal
    #
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    wph
    vy
    vx
    cA
    cB
    csb
    #
    wsbc
    #
    wb
    #
    @1
    @2
    vx
    vz
    cv
    #
    wsbc
    #
    wph
    vy
    vx
    @7
    cB
    csb
    #
    wsbc
    #
    wb
    #
    wi
    @1
    @6
    wi
    vz
    cA
    cV
    @7
    cA
    wceq
    #
    @11
    @6
    @1
    @12
    @8
    @3
    @10
    @5
    @2
    vx
    @7
    cA
    dfsbcq
    @12
    wph
    vy
    @9
    @4
    vx
    @7
    cA
    cB
    csbeq1
    sbceq1d
    bibi12d
    imbi2d
    @1
    @2
    @10
    vx
    @7
    cvv
    @7
    cvv
    wcel
    @1
    vz
    vex
    a1i
    vx
    cv
    @7
    wceq
    #
    @2
    @10
    wb
    @1
    @13
    wph
    vy
    cB
    @9
    vx
    @7
    cB
    csbeq1a
    sbceq1d
    adantl
    @0
    vx
    vy
    wph
    vx
    nfnf1
    nfal
    @1
    wph
    vx
    vy
    @9
    @0
    vy
    nfa1
    vx
    @9
    wnfc
    @1
    vx
    @7
    cB
    nfcsb1v
    a1i
    @0
    vy
    sp
    nfsbcd
    sbciedf
    vtoclg
    imp
end
