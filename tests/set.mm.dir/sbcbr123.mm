include "wbr.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "csb.mm"
include "sbcex.mm"
include "wn.mm"
include "c0.mm"
include "br0.mm"
include "csbprc.mm"
include "breqd.mm"
include "mtbiri.mm"
include "con4i.mm"
include "wsb.mm"
include "cv.mm"
include "dfsbcq2.mm"
include "wceq.mm"
include "csbeq1.mm"
include "breq123d.mm"
include "nfcsb1v.mm"
include "nfbr.mm"
include "weq.mm"
include "csbeq1a.mm"
include "sbie.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcbr123
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vy: setvar y


  assert |- ( [. A / x ]. B R C <-> [_ A / x ]_ B [_ A / x ]_ R [_ A / x ]_ C )

  proof
    cB
    cC
    cR
    wbr
    #
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
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
    vx
    cA
    cR
    csb
    #
    wbr
    #
    @0
    vx
    cA
    sbcex
    @2
    @6
    @2
    wn
    #
    @6
    @3
    @4
    c0
    wbr
    @3
    @4
    br0
    @7
    @5
    c0
    @3
    @4
    vx
    cA
    cR
    csbprc
    breqd
    mtbiri
    con4i
    @0
    vx
    vy
    wsb
    vx
    vy
    cv
    #
    cB
    csb
    #
    vx
    @8
    cC
    csb
    #
    vx
    @8
    cR
    csb
    #
    wbr
    #
    @1
    @6
    vy
    cA
    cvv
    @0
    vx
    vy
    cA
    dfsbcq2
    @8
    cA
    wceq
    @9
    @3
    @10
    @4
    @11
    @5
    vx
    @8
    cA
    cB
    csbeq1
    vx
    @8
    cA
    cR
    csbeq1
    vx
    @8
    cA
    cC
    csbeq1
    breq123d
    @0
    @12
    vx
    vy
    vx
    @9
    @10
    @11
    vx
    @8
    cB
    nfcsb1v
    vx
    @8
    cR
    nfcsb1v
    vx
    @8
    cC
    nfcsb1v
    nfbr
    vx
    vy
    weq
    cB
    @9
    cC
    @10
    cR
    @11
    vx
    @8
    cB
    csbeq1a
    vx
    @8
    cR
    csbeq1a
    vx
    @8
    cC
    csbeq1a
    breq123d
    sbie
    vtoclbg
    pm5.21nii
end
