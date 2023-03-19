include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "csubg.mm"
include "cfv.mm"
include "wb.mm"
include "slwsubg.mm"
include "slwispgp.mm"
include "mpdan.mm"
include "mpbiri.mm"
include "simprd.mm"

theorem slwpgp
  let cP: class P
  let cS: class S
  let cG: class G
  let cH: class H
  assume slwpgp.1: |- S = ( G |`s H )


  assert |- ( H e. ( P pSyl G ) -> P pGrp S )

  proof
    cH
    cP
    cG
    cslw
    co
    wcel
    #
    cH
    cH
    wss
    #
    cP
    cS
    cpgp
    wbr
    #
    @0
    @1
    @2
    wa
    #
    cH
    cH
    wceq
    #
    cH
    eqid
    @0
    cH
    cG
    csubg
    cfv
    wcel
    @3
    @4
    wb
    cP
    cG
    cH
    slwsubg
    cP
    cS
    cG
    cH
    cH
    slwpgp.1
    slwispgp
    mpdan
    mpbiri
    simprd
end
