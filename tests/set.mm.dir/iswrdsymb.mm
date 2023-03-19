include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "wfn.mm"
include "wrdfn.mm"
include "anim1i.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "iswrdi.mm"
include "syl.mm"

theorem iswrdsymb
  let vi: setvar i
  let cV: class V
  let cW: class W

  disjoint V i
  disjoint W i
  assert |- ( ( W e. Word _V /\ A. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) e. V ) -> W e. Word V )

  proof
    cW
    cvv
    cword
    wcel
    #
    vi
    cv
    cW
    cfv
    cV
    wcel
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    @2
    cV
    cW
    wf
    #
    cW
    cV
    cword
    wcel
    @4
    cW
    @2
    wfn
    #
    @3
    wa
    @5
    @0
    @6
    @3
    cvv
    cW
    wrdfn
    anim1i
    vi
    @2
    cV
    cW
    ffnfv
    sylibr
    cV
    @1
    cW
    iswrdi
    syl
end
