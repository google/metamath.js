include "wfun.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "ctpos.mm"
include "funmpt.mm"
include "funco.mm"
include "mpan2.mm"
include "df-tpos.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem tposfun
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Fun F -> Fun tpos F )

  proof
    cF
    wfun
    #
    cF
    vx
    cF
    cdm
    ccnv
    c0
    csn
    cun
    #
    vx
    cv
    csn
    ccnv
    cuni
    #
    cmpt
    #
    ccom
    #
    wfun
    #
    cF
    ctpos
    #
    wfun
    @0
    @3
    wfun
    @5
    vx
    @1
    @2
    funmpt
    cF
    @3
    funco
    mpan2
    @6
    @4
    vx
    cF
    df-tpos
    funeqi
    sylibr
end
