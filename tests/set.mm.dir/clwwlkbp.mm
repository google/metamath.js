include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "elfvex.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "eqid.mm"
include "isclwwlk.mm"
include "simp1bi.mm"
include "3anass.mm"
include "sylanbrc.mm"

theorem clwwlkbp
  let cG: class G
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume clwwlkbp.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( ClWWalks ` G ) -> ( G e. _V /\ W e. Word V /\ W =/= (/) ) )

  proof
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    cG
    cvv
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    @1
    @2
    @3
    w3a
    cW
    cG
    cclwwlk
    elfvex
    @0
    @4
    vi
    cv
    #
    cW
    cfv
    @5
    c1
    caddc
    co
    cW
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cW
    chash
    cfv
    c1
    cmin
    co
    cfzo
    co
    wral
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    cpr
    @6
    wcel
    vi
    @6
    cG
    cV
    cW
    clwwlkbp.v
    @6
    eqid
    isclwwlk
    simp1bi
    @1
    @2
    @3
    3anass
    sylanbrc
end
