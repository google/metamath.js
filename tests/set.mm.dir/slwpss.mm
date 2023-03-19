include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wpss.mm"
include "w3a.mm"
include "cpgp.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "simp3.mm"
include "pssned.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "pssssd.mm"
include "biantrurd.mm"
include "wb.mm"
include "slwispgp.mm"
include "3adant3.mm"
include "bitrd.mm"
include "necon3bbid.mm"
include "mpbird.mm"

theorem slwpss
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


  assert |- ( ( H e. ( P pSyl G ) /\ K e. ( SubGrp ` G ) /\ H C. K ) -> -. P pGrp S )

  proof
    cH
    cP
    cG
    cslw
    co
    wcel
    #
    cK
    cG
    csubg
    cfv
    wcel
    #
    cH
    cK
    wpss
    #
    w3a
    #
    cP
    cS
    cpgp
    wbr
    #
    wn
    cH
    cK
    wne
    @3
    cH
    cK
    @0
    @1
    @2
    simp3
    #
    pssned
    @3
    @4
    cH
    cK
    @3
    @4
    cH
    cK
    wss
    #
    @4
    wa
    #
    cH
    cK
    wceq
    #
    @3
    @6
    @4
    @3
    cH
    cK
    @5
    pssssd
    biantrurd
    @0
    @1
    @7
    @8
    wb
    @2
    cP
    cS
    cG
    cH
    cK
    slwispgp.1
    slwispgp
    3adant3
    bitrd
    necon3bbid
    mpbird
end
