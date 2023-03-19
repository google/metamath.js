include "cumgr.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "crn.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "rnresi.mm"
include "wnel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "simpr.mm"
include "adantr.mm"
include "cuhgr.mm"
include "cedg.mm"
include "umgruhgr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cvtx.mm"
include "edguhgr.mm"
include "elpwi.mm"
include "syl6sseqr.mm"
include "syl.mm"
include "syl2an.mm"
include "ad4ant13.mm"
include "elpwdifsn.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "elrabi.mm"
include "syl6eleq.mm"
include "edgumgr.mm"
include "simprd.mm"
include "syl5com.mm"
include "eleq2s.mm"
include "impcom.mm"
include "ssrabdv.mm"

theorem umgrres1lem
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  assume upgrres1.v: |- V = ( Vtx ` G )
  assume upgrres1.e: |- E = ( Edg ` G )
  assume upgrres1.f: |- F = { e e. E | N e/ e }

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint F p
  disjoint G p
  disjoint N p
  disjoint V p
  disjoint e p
  assert |- ( ( G e. UMGraph /\ N e. V ) -> ran ( _I |` F ) C_ { p e. ~P ( V \ { N } ) | ( # ` p ) = 2 } )

  proof
    cG
    cumgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cid
    cF
    cres
    crn
    cF
    vp
    cv
    #
    chash
    cfv
    c2
    wceq
    #
    vp
    cV
    cN
    csn
    cdif
    cpw
    #
    crab
    cF
    rnresi
    @2
    @4
    vp
    @5
    cF
    @2
    cF
    cN
    ve
    cv
    #
    wnel
    #
    ve
    cE
    crab
    #
    @5
    upgrres1.f
    @2
    @7
    @6
    @5
    wcel
    #
    wi
    #
    ve
    cE
    wral
    @8
    @5
    wss
    @2
    @10
    ve
    cE
    @2
    @6
    cE
    wcel
    #
    wa
    #
    @7
    @9
    @12
    @7
    wa
    @11
    @6
    cV
    wss
    #
    @7
    @9
    @12
    @11
    @7
    @2
    @11
    simpr
    adantr
    @0
    @11
    @13
    @1
    @7
    @0
    cG
    cuhgr
    wcel
    #
    @6
    cG
    cedg
    cfv
    #
    wcel
    #
    @13
    @11
    cG
    umgruhgr
    @11
    @16
    cE
    @15
    @6
    upgrres1.e
    eleq2i
    biimpi
    @14
    @16
    wa
    @6
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    @13
    @6
    cG
    edguhgr
    @19
    @6
    @17
    cV
    @6
    @17
    elpwi
    upgrres1.v
    syl6sseqr
    syl
    syl2an
    ad4ant13
    @12
    @7
    simpr
    cN
    @6
    cV
    cE
    elpwdifsn
    syl3anc
    ex
    ralrimiva
    @7
    ve
    cE
    @5
    rabss
    sylibr
    syl5eqss
    @3
    cF
    wcel
    @2
    @4
    @2
    @4
    wi
    @3
    @8
    cF
    @3
    @8
    wcel
    #
    @3
    @15
    wcel
    #
    @2
    @4
    @20
    @3
    cE
    @15
    @7
    ve
    @3
    cE
    elrabi
    upgrres1.e
    syl6eleq
    @0
    @21
    @4
    wi
    @1
    @0
    @21
    @4
    @0
    @21
    wa
    @3
    @18
    wcel
    @4
    @3
    cG
    edgumgr
    simprd
    ex
    adantr
    syl5com
    upgrres1.f
    eleq2s
    impcom
    ssrabdv
    syl5eqss
end
