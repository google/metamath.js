include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "sbgoldbalt.mm"
include "biimpi.mm"

theorem sbgoldbb
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint n p
  disjoint n q
  disjoint p q
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> A. n e. Even ( 2 < n -> E. p e. Prime E. q e. Prime n = ( p + q ) ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    @0
    cgbe
    wcel
    wi
    vn
    ceven
    wral
    c2
    @0
    clt
    wbr
    @0
    vp
    cv
    vq
    cv
    caddc
    co
    wceq
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    wi
    vn
    ceven
    wral
    vn
    vq
    vp
    sbgoldbalt
    biimpi
end
