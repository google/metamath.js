include "ccnv.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ccn.mm"
include "eqid.mm"
include "fcnre.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "cxr.mm"
include "clt.mm"
include "w3a.mm"
include "mnfxr.mm"
include "rexrd.mm"
include "adantr.mm"
include "elioc1.mm"
include "sylancr.mm"
include "simpr3.mm"
include "ffvelrnda.mm"
include "mnflt.mm"
include "syl.mm"
include "simpr.mm"
include "3jca.mm"
include "impbida.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrabf.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "syl6eqr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "iocmnfcld.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "cnclima.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem rfcnpre4
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let vs: setvar s
  assume rfcnpre4.1: |- F/_ t F
  assume rfcnpre4.2: |- K = ( topGen ` ran (,) )
  assume rfcnpre4.3: |- T = U. J
  assume rfcnpre4.4: |- A = { t e. T | ( F ` t ) <_ B }
  assume rfcnpre4.5: |- ( ph -> B e. RR )
  assume rfcnpre4.6: |- ( ph -> F e. ( J Cn K ) )

  disjoint B t
  disjoint T t
  disjoint s t
  disjoint B s
  disjoint F s
  disjoint T s
  disjoint ph s
  assert |- ( ph -> A e. ( Clsd ` J ) )

  proof
    wph
    cF
    ccnv
    cmnf
    cB
    cioc
    co
    #
    cima
    #
    cA
    cJ
    ccld
    cfv
    #
    wph
    @1
    vt
    cv
    #
    cF
    cfv
    #
    cB
    cle
    wbr
    #
    vt
    cT
    crab
    #
    cA
    wph
    vs
    @1
    @6
    wph
    vs
    cv
    #
    @1
    wcel
    #
    @7
    cT
    wcel
    #
    @7
    cF
    cfv
    #
    cB
    cle
    wbr
    #
    wa
    #
    @7
    @6
    wcel
    wph
    @8
    @9
    @10
    @0
    wcel
    #
    wa
    #
    @12
    wph
    cT
    cr
    cF
    wf
    cF
    cT
    wfn
    @8
    @14
    wb
    wph
    cJ
    cK
    ccn
    co
    #
    cT
    cF
    cJ
    cK
    rfcnpre4.2
    rfcnpre4.3
    @15
    eqid
    rfcnpre4.6
    fcnre
    #
    cT
    cr
    cF
    ffn
    cT
    @7
    @0
    cF
    elpreima
    3syl
    wph
    @9
    @13
    @11
    wph
    @9
    wa
    #
    @13
    @10
    cxr
    wcel
    #
    cmnf
    @10
    clt
    wbr
    #
    @11
    w3a
    #
    @11
    @17
    cmnf
    cxr
    wcel
    cB
    cxr
    wcel
    #
    @13
    @20
    wb
    mnfxr
    wph
    @21
    @9
    wph
    cB
    rfcnpre4.5
    rexrd
    adantr
    cmnf
    cB
    @10
    elioc1
    sylancr
    @17
    @20
    @11
    @17
    @18
    @19
    @11
    simpr3
    @17
    @11
    wa
    #
    @18
    @19
    @11
    @17
    @18
    @11
    @17
    @10
    wph
    cT
    cr
    @7
    cF
    @16
    ffvelrnda
    #
    rexrd
    adantr
    @22
    @10
    cr
    wcel
    #
    @19
    @17
    @24
    @11
    @23
    adantr
    @10
    mnflt
    syl
    @17
    @11
    simpr
    3jca
    impbida
    bitrd
    pm5.32da
    bitrd
    @5
    @11
    vt
    @7
    cT
    vt
    @7
    nfcv
    #
    vt
    cT
    nfcv
    vt
    @10
    cB
    cle
    vt
    @7
    cF
    rfcnpre4.1
    @25
    nffv
    vt
    cle
    nfcv
    vt
    cB
    nfcv
    nfbr
    vt
    vs
    weq
    @4
    @10
    cB
    cle
    @3
    @7
    cF
    fveq2
    breq1d
    elrabf
    syl6bbr
    eqrdv
    rfcnpre4.4
    syl6eqr
    wph
    cF
    @15
    wcel
    @0
    cK
    ccld
    cfv
    #
    wcel
    @1
    @2
    wcel
    rfcnpre4.6
    wph
    @0
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @26
    wph
    cB
    cr
    wcel
    @0
    @28
    wcel
    rfcnpre4.5
    cB
    iocmnfcld
    syl
    cK
    @27
    ccld
    rfcnpre4.2
    fveq2i
    syl6eleqr
    @0
    cF
    cJ
    cK
    cnclima
    syl2anc
    eqeltrrd
end
