include "ccnv.mm"
include "cpnf.mm"
include "cico.mm"
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
include "rexrd.mm"
include "adantr.mm"
include "pnfxr.mm"
include "elico1.mm"
include "sylancl.mm"
include "simpr2.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "ltpnf.mm"
include "syl.mm"
include "3jca.mm"
include "impbida.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrabf.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "syl6eqr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "icopnfcld.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "cnclima.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem rfcnpre3
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let vs: setvar s
  assume rfcnpre3.2: |- F/_ t F
  assume rfcnpre3.3: |- K = ( topGen ` ran (,) )
  assume rfcnpre3.4: |- T = U. J
  assume rfcnpre3.5: |- A = { t e. T | B <_ ( F ` t ) }
  assume rfcnpre3.6: |- ( ph -> B e. RR )
  assume rfcnpre3.8: |- ( ph -> F e. ( J Cn K ) )

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
    cB
    cpnf
    cico
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
    cB
    vt
    cv
    #
    cF
    cfv
    #
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
    cB
    @7
    cF
    cfv
    #
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
    rfcnpre3.3
    rfcnpre3.4
    @15
    eqid
    rfcnpre3.8
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
    @11
    @10
    cpnf
    clt
    wbr
    #
    w3a
    #
    @11
    @17
    cB
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    @13
    @20
    wb
    wph
    @21
    @9
    wph
    cB
    rfcnpre3.6
    rexrd
    adantr
    pnfxr
    cB
    cpnf
    @10
    elico1
    sylancl
    @17
    @20
    @11
    @17
    @18
    @11
    @19
    simpr2
    @17
    @11
    wa
    #
    @18
    @11
    @19
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
    @17
    @11
    simpr
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
    ltpnf
    syl
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
    cB
    @10
    cle
    vt
    cB
    nfcv
    vt
    cle
    nfcv
    vt
    @7
    cF
    rfcnpre3.2
    @25
    nffv
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
    breq2d
    elrabf
    syl6bbr
    eqrdv
    rfcnpre3.5
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
    rfcnpre3.8
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
    rfcnpre3.6
    cB
    icopnfcld
    syl
    cK
    @27
    ccld
    rfcnpre3.3
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
