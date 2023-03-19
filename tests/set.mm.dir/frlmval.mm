include "wcel.mm"
include "wa.mm"
include "cfrlm.mm"
include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "oveq12d.mm"
include "xpeq1.mm"
include "oveq2d.mm"
include "df-frlm.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem frlmval
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )


  assert |- ( ( R e. V /\ I e. W ) -> F = ( R (+)m ( I X. { ( ringLMod ` R ) } ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    cF
    cR
    cI
    cfrlm
    co
    #
    cR
    cI
    cR
    crglmod
    cfv
    #
    csn
    #
    cxp
    #
    cdsmm
    co
    #
    frlmval.f
    @0
    cR
    cvv
    wcel
    cI
    cvv
    wcel
    @2
    @6
    wceq
    @1
    cR
    cV
    elex
    cI
    cW
    elex
    vr
    vi
    cR
    cI
    cvv
    cvv
    vr
    cv
    #
    vi
    cv
    #
    @7
    crglmod
    cfv
    #
    csn
    #
    cxp
    #
    cdsmm
    co
    @6
    cfrlm
    cR
    @8
    @4
    cxp
    #
    cdsmm
    co
    @7
    cR
    wceq
    #
    @7
    cR
    @11
    @12
    cdsmm
    @13
    id
    @13
    @10
    @4
    @8
    @13
    @9
    @3
    @7
    cR
    crglmod
    fveq2
    sneqd
    xpeq2d
    oveq12d
    @8
    cI
    wceq
    @12
    @5
    cR
    cdsmm
    @8
    cI
    @4
    xpeq1
    oveq2d
    vi
    vr
    df-frlm
    cR
    @5
    cdsmm
    ovex
    ovmpt2
    syl2an
    syl5eq
end
