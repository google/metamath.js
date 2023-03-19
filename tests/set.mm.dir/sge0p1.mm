include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cxad.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "fzsuc.mm"
include "syl.mm"
include "mpteq1d.mm"
include "fveq2d.mm"
include "cvv.mm"
include "nfv.mm"
include "ovex.mm"
include "a1i.mm"
include "snex.mm"
include "cin.mm"
include "c0.mm"
include "fzp1disj.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "cicc.mm"
include "iccssxr.mm"
include "simpl.mm"
include "fzelp1.mm"
include "adantl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "iccleub.mm"
include "eliccxrd.mm"
include "elsni.mm"
include "simpr.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "3syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "sge0splitmpt.mm"
include "id.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "sge0snmpt.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem sge0p1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vx: setvar x
  assume sge0p1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume sge0p1.2: |- ( ( ph /\ k e. ( M ... ( N + 1 ) ) ) -> A e. ( 0 [,] +oo ) )
  assume sge0p1.3: |- ( k = ( N + 1 ) -> A = B )

  disjoint B k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. ( M ... ( N + 1 ) ) |-> A ) ) = ( ( sum^ ` ( k e. ( M ... N ) |-> A ) ) +e B ) )

  proof
    wph
    vk
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    cmpt
    #
    csumge0
    cfv
    vk
    cM
    cN
    cfz
    co
    #
    @0
    csn
    #
    cun
    #
    cA
    cmpt
    #
    csumge0
    cfv
    vk
    @3
    cA
    cmpt
    csumge0
    cfv
    #
    vk
    @4
    cA
    cmpt
    csumge0
    cfv
    #
    cxad
    co
    @7
    cB
    cxad
    co
    wph
    @2
    @6
    csumge0
    wph
    vk
    @1
    @5
    cA
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    @5
    wceq
    sge0p1.1
    cM
    cN
    fzsuc
    syl
    mpteq1d
    fveq2d
    wph
    vk
    @3
    @4
    cA
    cvv
    cvv
    wph
    vk
    nfv
    @3
    cvv
    wcel
    wph
    cM
    cN
    cfz
    ovex
    a1i
    @4
    cvv
    wcel
    wph
    @0
    snex
    a1i
    @3
    @4
    cin
    c0
    wceq
    wph
    cM
    cN
    fzp1disj
    a1i
    wph
    vk
    cv
    #
    @3
    wcel
    #
    wa
    #
    cc0
    cpnf
    cA
    cc0
    cxr
    wcel
    #
    @13
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @13
    pnfxr
    a1i
    #
    @13
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cA
    cc0
    cpnf
    iccssxr
    @13
    wph
    @11
    @1
    wcel
    #
    cA
    @18
    wcel
    #
    wph
    @12
    simpl
    @12
    @19
    wph
    @11
    cM
    cN
    fzelp1
    adantl
    sge0p1.2
    syl2anc
    #
    sseldi
    @13
    @14
    @16
    @20
    cc0
    cA
    cle
    wbr
    @15
    @17
    @21
    cc0
    cpnf
    cA
    iccgelb
    syl3anc
    @13
    @14
    @16
    @20
    cA
    cpnf
    cle
    wbr
    @15
    @17
    @21
    cc0
    cpnf
    cA
    iccleub
    syl3anc
    eliccxrd
    wph
    @11
    @4
    wcel
    #
    wa
    #
    wph
    @19
    @20
    wph
    @22
    simpl
    #
    @23
    wph
    @11
    @0
    wceq
    #
    @19
    @24
    @22
    @25
    wph
    @11
    @0
    elsni
    adantl
    wph
    @25
    wa
    @11
    @0
    @1
    wph
    @25
    simpr
    wph
    @0
    @1
    wcel
    #
    @25
    wph
    @10
    @0
    @9
    wcel
    @26
    sge0p1.1
    cM
    cN
    peano2uz
    cM
    @0
    eluzfz2
    3syl
    #
    adantr
    eqeltrd
    syl2anc
    sge0p1.2
    syl2anc
    sge0splitmpt
    wph
    @8
    cB
    @7
    cxad
    wph
    @0
    cA
    cB
    vk
    cvv
    @0
    cvv
    wcel
    #
    wph
    cN
    c1
    caddc
    ovex
    #
    a1i
    wph
    wph
    @26
    cB
    @18
    wcel
    #
    wph
    id
    @27
    @28
    wph
    @26
    wa
    #
    @30
    wi
    #
    @29
    wph
    @19
    wa
    #
    @20
    wi
    @32
    vk
    @0
    cvv
    @25
    @33
    @31
    @20
    @30
    @25
    @19
    @26
    wph
    @11
    @0
    @1
    eleq1
    anbi2d
    @25
    cA
    cB
    @18
    sge0p1.3
    eleq1d
    imbi12d
    sge0p1.2
    vtoclg
    ax-mp
    syl2anc
    sge0p1.3
    sge0snmpt
    oveq2d
    3eqtrd
end
