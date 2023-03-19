include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "clm.mm"
include "wbr.mm"
include "cv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "simp2.mm"
include "simp3.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "wa.mm"
include "idd.mm"
include "ralrimdva.mm"
include "wceq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "ralrimivw.mm"
include "simp1.mm"
include "wf.mm"
include "fconst6g.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "lmbrf.mm"
include "mpbir2and.mm"

theorem lmconst
  let cP: class P
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  assume lmconst.2: |- Z = ( ZZ>= ` M )


  assert |- ( ( J e. ( TopOn ` X ) /\ P e. X /\ M e. ZZ ) -> ( Z X. { P } ) ( ~~>t ` J ) P )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cZ
    cP
    csn
    cxp
    #
    cP
    cJ
    clm
    cfv
    wbr
    @1
    cP
    vu
    cv
    wcel
    #
    @5
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    @0
    @1
    @2
    simp2
    #
    @3
    @10
    vu
    cJ
    @3
    cM
    cZ
    wcel
    @5
    @5
    vk
    cM
    cuz
    cfv
    #
    wral
    #
    @9
    @3
    cM
    @12
    cZ
    @3
    @2
    cM
    @12
    wcel
    @0
    @1
    @2
    simp3
    #
    cM
    uzid
    syl
    lmconst.2
    syl6eleqr
    @3
    @5
    @5
    vk
    @12
    @3
    vk
    cv
    #
    @12
    wcel
    wa
    @5
    idd
    ralrimdva
    @8
    @13
    vj
    cM
    cZ
    @6
    cM
    wceq
    @5
    vk
    @7
    @12
    @6
    cM
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    ralrimivw
    @3
    vu
    cP
    cP
    vj
    vk
    @4
    cJ
    cM
    cX
    cZ
    @0
    @1
    @2
    simp1
    lmconst.2
    @14
    @3
    @1
    cZ
    cX
    @4
    wf
    @11
    cZ
    cP
    cX
    fconst6g
    syl
    @3
    @1
    @15
    cZ
    wcel
    @15
    @4
    cfv
    cP
    wceq
    @11
    cZ
    cP
    @15
    cX
    fvconst2g
    sylan
    lmbrf
    mpbir2and
end
