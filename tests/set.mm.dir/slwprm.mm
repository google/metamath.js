include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "cprime.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "isslw.mm"
include "simp1bi.mm"

theorem slwprm
  let cP: class P
  let cG: class G
  let cH: class H
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vp: setvar p
  let cK: class K
  let cS: class S


  assert |- ( H e. ( P pSyl G ) -> P e. Prime )

  proof
    cH
    cP
    cG
    cslw
    co
    wcel
    cP
    cprime
    wcel
    cH
    cG
    csubg
    cfv
    #
    wcel
    cH
    vk
    cv
    #
    wss
    cP
    cG
    @1
    cress
    co
    cpgp
    wbr
    wa
    cH
    @1
    wceq
    wb
    vk
    @0
    wral
    cP
    vk
    cG
    cH
    isslw
    simp1bi
end
