include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "cple.mm"
include "eqid.mm"
include "cbs.mm"
include "wceq.mm"
include "ipobas.mm"
include "adantr.mm"
include "club.mm"
include "a1i.mm"
include "cpo.mm"
include "ipopos.mm"
include "simpr.mm"
include "uniss.mm"
include "adantl.mm"
include "mreuni.mm"
include "sseqtrd.mm"
include "mrccl.mm"
include "syldan.mm"
include "cv.mm"
include "wbr.mm"
include "elssuni.mm"
include "mrcssid.mm"
include "sylan9ssr.mm"
include "wb.mm"
include "simpll.mm"
include "sselda.mm"
include "ipole.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wral.mm"
include "w3a.mm"
include "simp1l.mm"
include "simplll.mm"
include "simplr.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "3impia.mm"
include "unissb.mm"
include "sylibr.mm"
include "simp2.mm"
include "mrcsscl.mm"
include "3ad2ant1.mm"
include "poslubdg.mm"

theorem mrelatlub
  let cC: class C
  let cU: class U
  let cF: class F
  let cI: class I
  let cL: class L
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  assume mreclat.i: |- I = ( toInc ` C )
  assume mrelatlub.f: |- F = ( mrCls ` C )
  assume mrelatlub.l: |- L = ( lub ` I )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ C ) -> ( L ` U ) = ( F ` U. U ) )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cU
    cC
    wss
    #
    wa
    #
    vx
    vy
    cC
    cU
    cU
    cuni
    #
    cF
    cfv
    #
    cL
    cI
    cI
    cple
    cfv
    #
    @6
    eqid
    #
    @1
    cC
    cI
    cbs
    cfv
    wceq
    @2
    cC
    cI
    @0
    mreclat.i
    ipobas
    adantr
    cL
    cI
    club
    cfv
    wceq
    @3
    mrelatlub.l
    a1i
    cI
    cpo
    wcel
    @3
    cC
    cI
    mreclat.i
    ipopos
    a1i
    @1
    @2
    simpr
    #
    @1
    @2
    @4
    cX
    wss
    #
    @5
    cC
    wcel
    #
    @3
    @4
    cC
    cuni
    #
    cX
    @2
    @4
    @11
    wss
    @1
    cU
    cC
    uniss
    adantl
    @1
    @11
    cX
    wceq
    @2
    cC
    cX
    mreuni
    adantr
    sseqtrd
    #
    cC
    @4
    cF
    cX
    mrelatlub.f
    mrccl
    syldan
    #
    @3
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    @14
    @5
    @6
    wbr
    #
    @14
    @5
    wss
    #
    @15
    @3
    @14
    @4
    @5
    @14
    cU
    elssuni
    @1
    @2
    @9
    @4
    @5
    wss
    @12
    cC
    @4
    cF
    cX
    mrelatlub.f
    mrcssid
    syldan
    sylan9ssr
    @16
    @1
    @14
    cC
    wcel
    #
    @10
    @17
    @18
    wb
    @1
    @2
    @15
    simpll
    @3
    cU
    cC
    @14
    @8
    sselda
    @3
    @10
    @15
    @13
    adantr
    cC
    cI
    @6
    @0
    @14
    @5
    mreclat.i
    @7
    ipole
    syl3anc
    mpbird
    @3
    vy
    cv
    #
    cC
    wcel
    #
    @14
    @20
    @6
    wbr
    #
    vx
    cU
    wral
    #
    w3a
    #
    @5
    @20
    @6
    wbr
    #
    @5
    @20
    wss
    #
    @24
    @1
    @4
    @20
    wss
    #
    @21
    @26
    @1
    @2
    @21
    @23
    simp1l
    #
    @24
    @14
    @20
    wss
    #
    vx
    cU
    wral
    #
    @27
    @3
    @21
    @23
    @30
    @3
    @21
    wa
    #
    @22
    @29
    vx
    cU
    @31
    @15
    wa
    #
    @22
    @29
    @32
    @1
    @19
    @21
    @22
    @29
    wb
    @1
    @2
    @21
    @15
    simplll
    @31
    cU
    cC
    @14
    @1
    @2
    @21
    simplr
    sselda
    @3
    @21
    @15
    simplr
    cC
    cI
    @6
    @0
    @14
    @20
    mreclat.i
    @7
    ipole
    syl3anc
    biimpd
    ralimdva
    3impia
    vx
    cU
    @20
    unissb
    sylibr
    @3
    @21
    @23
    simp2
    #
    cC
    @4
    cF
    @20
    cX
    mrelatlub.f
    mrcsscl
    syl3anc
    @24
    @1
    @10
    @21
    @25
    @26
    wb
    @28
    @3
    @21
    @10
    @23
    @13
    3ad2ant1
    @33
    cC
    cI
    @6
    @0
    @5
    @20
    mreclat.i
    @7
    ipole
    syl3anc
    mpbird
    poslubdg
end
