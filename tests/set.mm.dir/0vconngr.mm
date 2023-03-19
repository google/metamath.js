include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cconngr.mm"
include "cv.mm"
include "cpthson.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wral.mm"
include "rzal.mm"
include "adantl.mm"
include "wb.mm"
include "eqid.mm"
include "isconngr.mm"
include "adantr.mm"
include "mpbird.mm"

theorem 0vconngr
  let cG: class G
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) ) -> G e. ConnGraph )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    wa
    cG
    cconngr
    wcel
    #
    vf
    cv
    vp
    cv
    vk
    cv
    vn
    cv
    cG
    cpthson
    cfv
    co
    wbr
    vp
    wex
    vf
    wex
    vn
    @1
    wral
    #
    vk
    @1
    wral
    #
    @2
    @5
    @0
    @4
    vk
    @1
    rzal
    adantl
    @0
    @3
    @5
    wb
    @2
    vf
    vk
    vn
    cG
    @1
    cW
    vp
    @1
    eqid
    isconngr
    adantr
    mpbird
end
