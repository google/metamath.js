include "crg.mm"
include "cv.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "cin.mm"
include "crh.mm"
include "dfrhm2.mm"
include "elmpt2cl1.mm"

theorem rhmrcl1
  let cR: class R
  let cS: class S
  let cF: class F
  let vr: setvar r
  let vs: setvar s


  assert |- ( F e. ( R RingHom S ) -> R e. Ring )

  proof
    vr
    vs
    crg
    crg
    vr
    cv
    #
    vs
    cv
    #
    cghm
    co
    @0
    cmgp
    cfv
    @1
    cmgp
    cfv
    cmhm
    co
    cin
    cR
    cS
    crh
    cF
    vs
    vr
    dfrhm2
    elmpt2cl1
end
