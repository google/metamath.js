include "cipo.mm"
include "cfv.mm"
include "cdrs.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "cbs.mm"
include "wrex.mm"
include "cuni.mm"
include "simp2.mm"
include "wceq.mm"
include "cvv.mm"
include "ipodrscl.mm"
include "eqid.mm"
include "ipobas.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "sseqtrd.mm"
include "drsdirfi.mm"
include "syld3an2.mm"
include "rexeqdv.mm"
include "wa.mm"
include "wb.mm"
include "adantr.mm"
include "sselda.mm"
include "adantrl.mm"
include "simprl.mm"
include "ipole.mm"
include "syl3anc.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "unissb.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "bitr3d.mm"
include "mpbid.mm"

theorem ipodrsfi
  let vz: setvar z
  let cA: class A
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y

  disjoint A z
  disjoint X z
  disjoint A w
  disjoint w z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint X w
  disjoint x z
  disjoint y z
  assert |- ( ( ( toInc ` A ) e. Dirset /\ X C_ A /\ X e. Fin ) -> E. z e. A U. X C_ z )

  proof
    cA
    cipo
    cfv
    #
    cdrs
    wcel
    #
    cX
    cA
    wss
    #
    cX
    cfn
    wcel
    #
    w3a
    #
    vw
    cv
    #
    vz
    cv
    #
    @0
    cple
    cfv
    #
    wbr
    #
    vw
    cX
    wral
    #
    vz
    @0
    cbs
    cfv
    #
    wrex
    #
    cX
    cuni
    @6
    wss
    #
    vz
    cA
    wrex
    #
    @1
    cX
    @10
    wss
    @2
    @3
    @11
    @4
    cX
    cA
    @10
    @1
    @2
    @3
    simp2
    #
    @1
    @2
    cA
    @10
    wceq
    #
    @3
    @1
    cA
    cvv
    wcel
    #
    @15
    cA
    ipodrscl
    #
    cA
    @0
    cvv
    @0
    eqid
    #
    ipobas
    syl
    3ad2ant1
    #
    sseqtrd
    vz
    vw
    @10
    @0
    @7
    cX
    @10
    eqid
    @7
    eqid
    #
    drsdirfi
    syld3an2
    @4
    @9
    vz
    cA
    wrex
    @11
    @13
    @4
    @9
    vz
    cA
    @10
    @19
    rexeqdv
    @4
    @9
    @12
    vz
    cA
    @4
    @6
    cA
    wcel
    #
    wa
    #
    @9
    @5
    @6
    wss
    #
    vw
    cX
    wral
    @12
    @22
    @8
    @23
    vw
    cX
    @4
    @21
    @5
    cX
    wcel
    #
    @8
    @23
    wb
    #
    @4
    @21
    @24
    wa
    #
    wa
    @16
    @5
    cA
    wcel
    #
    @21
    @25
    @4
    @16
    @26
    @1
    @2
    @16
    @3
    @17
    3ad2ant1
    adantr
    @4
    @24
    @27
    @21
    @4
    cX
    cA
    @5
    @14
    sselda
    adantrl
    @4
    @21
    @24
    simprl
    cA
    @0
    @7
    cvv
    @5
    @6
    @18
    @20
    ipole
    syl3anc
    anassrs
    ralbidva
    vw
    cX
    @6
    unissb
    syl6bbr
    rexbidva
    bitr3d
    mpbid
end
