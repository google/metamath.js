include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "c6.mm"
include "cuz.mm"
include "cfv.mm"
include "sbgoldbm.mm"
include "c2.mm"
include "mogoldbb.mm"
include "sbgoldbalt.mm"
include "sylibr.mm"
include "impbii.mm"

theorem sbgoldbmb
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k

  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) <-> A. n e. ( ZZ>= ` 6 ) E. p e. Prime E. q e. Prime E. r e. Prime n = ( ( p + q ) + r ) )

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
    #
    @0
    vp
    cv
    vq
    cv
    caddc
    co
    #
    vr
    cv
    caddc
    co
    wceq
    vr
    cprime
    wrex
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vn
    c6
    cuz
    cfv
    wral
    #
    vn
    vr
    vq
    vp
    sbgoldbm
    @3
    c2
    @0
    clt
    wbr
    @0
    @2
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
    @1
    vn
    vr
    vq
    vp
    mogoldbb
    vn
    vq
    vp
    sbgoldbalt
    sylibr
    impbii
end
