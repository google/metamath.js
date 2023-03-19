include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "cab.mm"
include "csb.mm"
include "sbcex.mm"
include "elex.mm"
include "cv.mm"
include "abid.mm"
include "sbcbii.mm"
include "sbcel12.mm"
include "csbvarg.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "syl5bbr.mm"
include "pm5.21nii.mm"

theorem sbccsb2
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. ph <-> A e. [_ A / x ]_ { x | ph } )

  proof
    wph
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
    cA
    vx
    cA
    wph
    vx
    cab
    #
    csb
    #
    wcel
    #
    wph
    vx
    cA
    sbcex
    cA
    @3
    elex
    @0
    vx
    cv
    #
    @2
    wcel
    #
    vx
    cA
    wsbc
    #
    @1
    @4
    @6
    wph
    vx
    cA
    wph
    vx
    abid
    sbcbii
    @7
    vx
    cA
    @5
    csb
    #
    @3
    wcel
    @1
    @4
    vx
    cA
    @5
    @2
    sbcel12
    @1
    @8
    cA
    @3
    vx
    cA
    cvv
    csbvarg
    eleq1d
    syl5bb
    syl5bbr
    pm5.21nii
end
