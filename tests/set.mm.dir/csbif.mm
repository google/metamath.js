include "cvv.mm"
include "wcel.mm"
include "cif.mm"
include "csb.mm"
include "wsbc.mm"
include "wceq.mm"
include "cv.mm"
include "wsb.mm"
include "csbeq1.mm"
include "dfsbcq2.mm"
include "ifbieq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfs1v.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "weq.mm"
include "sbequ12.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "ifeq12d.mm"
include "ifid.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- [_ A / x ]_ if ( ph , B , C ) = if ( [. A / x ]. ph , [_ A / x ]_ B , [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    wph
    cB
    cC
    cif
    #
    csb
    #
    wph
    vx
    cA
    wsbc
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cif
    #
    wceq
    #
    vx
    vy
    cv
    #
    @1
    csb
    #
    wph
    vx
    vy
    wsb
    #
    vx
    @8
    cB
    csb
    #
    vx
    @8
    cC
    csb
    #
    cif
    #
    wceq
    @7
    vy
    cA
    cvv
    @8
    cA
    wceq
    #
    @9
    @2
    @13
    @6
    vx
    @8
    cA
    @1
    csbeq1
    @14
    @10
    @3
    @11
    @12
    @4
    @5
    wph
    vx
    vy
    cA
    dfsbcq2
    vx
    @8
    cA
    cB
    csbeq1
    vx
    @8
    cA
    cC
    csbeq1
    ifbieq12d
    eqeq12d
    vx
    @8
    @1
    @13
    vy
    vex
    @10
    vx
    @11
    @12
    wph
    vx
    vy
    nfs1v
    vx
    @8
    cB
    nfcsb1v
    vx
    @8
    cC
    nfcsb1v
    nfif
    vx
    vy
    weq
    wph
    @10
    cB
    cC
    @11
    @12
    wph
    vx
    vy
    sbequ12
    vx
    @8
    cB
    csbeq1a
    vx
    @8
    cC
    csbeq1a
    ifbieq12d
    csbief
    vtoclg
    @0
    wn
    #
    @2
    c0
    @6
    vx
    cA
    @1
    csbprc
    @15
    @6
    @3
    c0
    c0
    cif
    c0
    @15
    @3
    @4
    c0
    @5
    c0
    vx
    cA
    cB
    csbprc
    vx
    cA
    cC
    csbprc
    ifeq12d
    @3
    c0
    ifid
    syl6req
    eqtrd
    pm2.61i
end
