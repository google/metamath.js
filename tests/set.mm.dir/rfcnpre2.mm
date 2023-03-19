include "ccnv.mm"
include "cmnf.mm"
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
include "ccn.mm"
include "eqid.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "cxr.mm"
include "elioomnf.mm"
include "syl.mm"
include "baibd.mm"
include "syldan.mm"
include "pm5.32da.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "rabid.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrd.mm"
include "syl6eqr.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "syl6eleqr.mm"
include "cnima.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem rfcnpre2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume rfcnpre2.1: |- F/_ x B
  assume rfcnpre2.2: |- F/_ x F
  assume rfcnpre2.3: |- F/ x ph
  assume rfcnpre2.4: |- K = ( topGen ` ran (,) )
  assume rfcnpre2.5: |- X = U. J
  assume rfcnpre2.6: |- A = { x e. X | ( F ` x ) < B }
  assume rfcnpre2.7: |- ( ph -> B e. RR* )
  assume rfcnpre2.8: |- ( ph -> F e. ( J Cn K ) )


  assert |- ( ph -> A e. J )

  proof
    wph
    cF
    ccnv
    #
    cmnf
    cB
    cioo
    co
    #
    cima
    #
    cA
    cJ
    wph
    @2
    vx
    cv
    #
    cF
    cfv
    #
    cB
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
    rfcnpre2.3
    vx
    @0
    @1
    vx
    cF
    rfcnpre2.2
    nfcnv
    vx
    cmnf
    cB
    cioo
    vx
    cmnf
    nfcv
    vx
    cioo
    nfcv
    rfcnpre2.1
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
    cJ
    cK
    ccn
    co
    #
    cX
    cF
    cJ
    cK
    rfcnpre2.4
    rfcnpre2.5
    @14
    eqid
    rfcnpre2.8
    fcnre
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
    rfcnpre2.7
    cB
    @4
    elioomnf
    syl
    baibd
    syldan
    pm5.32da
    wph
    cX
    cr
    cF
    wf
    cF
    cX
    wfn
    @11
    @9
    wb
    @15
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
    rfcnpre2.6
    syl6eqr
    wph
    cF
    @14
    wcel
    @1
    cK
    wcel
    @2
    cJ
    wcel
    rfcnpre2.8
    wph
    @1
    cioo
    crn
    ctg
    cfv
    #
    cK
    @1
    @16
    wcel
    wph
    cmnf
    cB
    iooretop
    a1i
    rfcnpre2.4
    syl6eleqr
    @1
    cF
    cJ
    cK
    cnima
    syl2anc
    eqeltrrd
end
