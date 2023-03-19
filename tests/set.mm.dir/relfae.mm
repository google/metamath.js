include "cvv.mm"
include "wcel.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wa.mm"
include "cfae.mm"
include "co.mm"
include "wrel.mm"
include "cv.mm"
include "cdm.mm"
include "cmap.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "cae.mm"
include "copab.mm"
include "relopab.mm"
include "faeval.mm"
include "releqd.mm"
include "mpbiri.mm"

theorem relfae
  let cR: class R
  let cM: class M
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x


  assert |- ( ( R e. _V /\ M e. U. ran measures ) -> Rel ( R ~ae M ) )

  proof
    cR
    cvv
    wcel
    cM
    cmeas
    crn
    cuni
    wcel
    wa
    #
    cR
    cM
    cfae
    co
    #
    wrel
    vf
    cv
    #
    cR
    cdm
    cM
    cdm
    cuni
    #
    cmap
    co
    #
    wcel
    vg
    cv
    #
    @4
    wcel
    wa
    vx
    cv
    #
    @2
    cfv
    @6
    @5
    cfv
    cR
    wbr
    vx
    @3
    crab
    cM
    cae
    wbr
    wa
    #
    vf
    vg
    copab
    #
    wrel
    @7
    vf
    vg
    relopab
    @0
    @1
    @8
    vx
    cR
    vf
    vg
    cM
    faeval
    releqd
    mpbiri
end
