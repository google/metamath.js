include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "nfcnv.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfima.mm"
include "nfrab1.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wb.mm"
include "wf.mm"
include "wral.mm"
include "ccn.mm"
include "ctopon.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cntop1.mm"
include "syl.mm"
include "istopon.mm"
include "sylanblrc.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "iscn.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffvelrnda.mm"
include "cxr.mm"
include "elioopnf.mm"
include "baibd.mm"
include "syldan.mm"
include "pm5.32da.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "rabid.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrd.mm"
include "syl6eqr.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "cnima.mm"
include "eqeltrrd.mm"

theorem rfcnpre1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume rfcnpre1.1: |- F/_ x B
  assume rfcnpre1.2: |- F/_ x F
  assume rfcnpre1.3: |- F/ x ph
  assume rfcnpre1.4: |- K = ( topGen ` ran (,) )
  assume rfcnpre1.5: |- X = U. J
  assume rfcnpre1.6: |- A = { x e. X | B < ( F ` x ) }
  assume rfcnpre1.7: |- ( ph -> B e. RR* )
  assume rfcnpre1.8: |- ( ph -> F e. ( J Cn K ) )


  assert |- ( ph -> A e. J )

  proof
    wph
    cF
    ccnv
    #
    cB
    cpnf
    cioo
    co
    #
    cima
    #
    cA
    cJ
    wph
    @2
    cB
    vx
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vx
    cX
    crab
    #
    cA
    wph
    vx
    @2
    @6
    rfcnpre1.3
    vx
    @0
    @1
    vx
    cF
    rfcnpre1.2
    nfcnv
    vx
    cB
    cpnf
    cioo
    rfcnpre1.1
    vx
    cioo
    nfcv
    vx
    cpnf
    nfcv
    nfov
    nfima
    @5
    vx
    cX
    nfrab1
    wph
    @3
    cX
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @7
    @5
    wa
    #
    @3
    @2
    wcel
    #
    @3
    @6
    wcel
    #
    wph
    @7
    @8
    @5
    wph
    @7
    @4
    cr
    wcel
    #
    @8
    @5
    wb
    wph
    cX
    cr
    @3
    cF
    wph
    cX
    cr
    cF
    wf
    #
    @0
    vy
    cv
    cima
    cJ
    wcel
    vy
    cK
    wral
    #
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @14
    @15
    wa
    #
    rfcnpre1.8
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cr
    ctopon
    cfv
    #
    wcel
    @16
    @17
    wb
    wph
    cJ
    ctop
    wcel
    #
    cX
    cJ
    cuni
    wceq
    @18
    wph
    @16
    @20
    rfcnpre1.8
    cF
    cJ
    cK
    cntop1
    syl
    rfcnpre1.5
    cX
    cJ
    istopon
    sylanblrc
    cK
    cioo
    crn
    ctg
    cfv
    #
    @19
    rfcnpre1.4
    retopon
    eqeltri
    vy
    cF
    cJ
    cK
    cX
    cr
    iscn
    sylancl
    mpbid
    simpld
    #
    ffvelrnda
    wph
    @8
    @13
    @5
    wph
    cB
    cxr
    wcel
    @8
    @13
    @5
    wa
    wb
    rfcnpre1.7
    cB
    @4
    elioopnf
    syl
    baibd
    syldan
    pm5.32da
    wph
    @14
    cF
    cX
    wfn
    @11
    @9
    wb
    @22
    cX
    cr
    cF
    ffn
    cX
    @3
    @1
    cF
    elpreima
    3syl
    @12
    @10
    wb
    wph
    @5
    vx
    cX
    rabid
    a1i
    3bitr4d
    eqrd
    rfcnpre1.6
    syl6eqr
    wph
    @16
    @1
    cK
    wcel
    @2
    cJ
    wcel
    rfcnpre1.8
    @1
    @21
    cK
    cB
    cpnf
    iooretop
    rfcnpre1.4
    eleqtrri
    @1
    cF
    cJ
    cK
    cnima
    sylancl
    eqeltrrd
end
