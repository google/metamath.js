include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cinftyexpi.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "crn.mm"
include "cccinfty.mm"
include "cv.mm"
include "cc.mm"
include "cop.mm"
include "df-bj-inftyexpi.mm"
include "funmpt2.mm"
include "jctl.mm"
include "opex.mm"
include "dmmpti.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "fvelrn.mm"
include "df-bj-ccinfty.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3syl.mm"

theorem bj-elccinfty
  let cA: class A
  let vx: setvar x


  assert |- ( A e. ( -u _pi (,] _pi ) -> ( inftyexpi ` A ) e. CCinfty )

  proof
    cA
    cpi
    cneg
    cpi
    cioc
    co
    #
    wcel
    cinftyexpi
    wfun
    #
    cA
    cinftyexpi
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cinftyexpi
    cfv
    #
    cinftyexpi
    crn
    #
    wcel
    #
    @5
    cccinfty
    wcel
    #
    @4
    cA
    @2
    @0
    @3
    @1
    vx
    @0
    vx
    cv
    #
    cc
    cop
    #
    cinftyexpi
    vx
    df-bj-inftyexpi
    #
    funmpt2
    jctl
    @2
    @0
    vx
    @0
    @10
    cinftyexpi
    @9
    cc
    opex
    @11
    dmmpti
    eqcomi
    eleq2s
    cA
    cinftyexpi
    fvelrn
    @7
    @8
    @6
    cccinfty
    @5
    cccinfty
    @6
    df-bj-ccinfty
    eqcomi
    eleq2i
    biimpi
    3syl
end
