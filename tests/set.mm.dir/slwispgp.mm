include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "csubg.mm"
include "cfv.mm"
include "wral.mm"
include "cprime.mm"
include "isslw.mm"
include "simp3bi.mm"
include "sseq2.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem slwispgp
  let cP: class P
  let cS: class S
  let cG: class G
  let cH: class H
  let cK: class K
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vp: setvar p
  assume slwispgp.1: |- S = ( G |`s K )


  assert |- ( ( H e. ( P pSyl G ) /\ K e. ( SubGrp ` G ) ) -> ( ( H C_ K /\ P pGrp S ) <-> H = K ) )

  proof
    cH
    cP
    cG
    cslw
    co
    wcel
    #
    cH
    vk
    cv
    #
    wss
    #
    cP
    cG
    @1
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    cH
    @1
    wceq
    #
    wb
    #
    vk
    cG
    csubg
    cfv
    #
    wral
    #
    cK
    @8
    wcel
    cH
    cK
    wss
    #
    cP
    cS
    cpgp
    wbr
    #
    wa
    #
    cH
    cK
    wceq
    #
    wb
    #
    @0
    cP
    cprime
    wcel
    cH
    @8
    wcel
    @9
    cP
    vk
    cG
    cH
    isslw
    simp3bi
    @7
    @14
    vk
    cK
    @8
    @1
    cK
    wceq
    #
    @5
    @12
    @6
    @13
    @15
    @2
    @10
    @4
    @11
    @1
    cK
    cH
    sseq2
    @15
    @3
    cS
    cP
    cpgp
    @15
    @3
    cG
    cK
    cress
    co
    cS
    @1
    cK
    cG
    cress
    oveq2
    slwispgp.1
    syl6eqr
    breq2d
    anbi12d
    @1
    cK
    cH
    eqeq2
    bibi12d
    rspccva
    sylan
end
