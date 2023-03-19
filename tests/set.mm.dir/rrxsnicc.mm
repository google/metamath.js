include "cv.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cixp.mm"
include "csn.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wfn.mm"
include "ixpfn.mm"
include "adantl.mm"
include "cr.mm"
include "cmap.mm"
include "elmapfn.mm"
include "syl.mm"
include "adantr.mm"
include "simpll.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvixpv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "iccssred.mm"
include "fvixp2.mm"
include "adantll.mm"
include "sseldd.mm"
include "rexrd.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "iccgelb.mm"
include "xrletrid.mm"
include "syl21anc.mm"
include "eqfnfvd.mm"
include "velsn.mm"
include "bicomi.mm"
include "ssd.mm"
include "wss.mm"
include "cvv.mm"
include "wral.mm"
include "w3a.mm"
include "elexd.mm"
include "leidd.mm"
include "eliccd.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "elixp2.mm"
include "sylibr.mm"
include "wb.mm"
include "snssg.mm"
include "mpbid.mm"
include "eqssd.mm"

theorem rrxsnicc
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  assume rrxsnicc.1: |- ( ph -> A e. ( RR ^m X ) )

  disjoint A k
  disjoint X k
  disjoint k ph
  disjoint A f
  disjoint A j
  disjoint f j
  disjoint f k
  disjoint j k
  disjoint X f
  disjoint X j
  disjoint f ph
  disjoint j ph
  disjoint k x
  assert |- ( ph -> X_ k e. X ( ( A ` k ) [,] ( A ` k ) ) = { A } )

  proof
    wph
    vk
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @1
    cicc
    co
    #
    cixp
    #
    cA
    csn
    #
    wph
    vf
    @3
    @4
    wph
    vf
    cv
    #
    @3
    wcel
    #
    wa
    #
    @5
    cA
    wceq
    #
    @5
    @4
    wcel
    #
    @7
    vj
    cX
    @5
    cA
    @6
    @5
    cX
    wfn
    wph
    vk
    cX
    @2
    @5
    ixpfn
    adantl
    wph
    cA
    cX
    wfn
    #
    @6
    wph
    cA
    cr
    cX
    cmap
    co
    #
    wcel
    #
    @10
    rrxsnicc.1
    cA
    cr
    cX
    elmapfn
    syl
    #
    adantr
    @7
    vj
    cv
    #
    cX
    wcel
    #
    wa
    wph
    @5
    vj
    cX
    @14
    cA
    cfv
    #
    @16
    cicc
    co
    #
    cixp
    #
    wcel
    #
    @15
    @14
    @5
    cfv
    #
    @16
    wceq
    wph
    @6
    @15
    simpll
    @6
    @19
    wph
    @15
    @6
    @19
    @3
    @18
    @5
    vk
    vj
    cX
    @2
    @17
    @0
    @14
    wceq
    @1
    @16
    @1
    @16
    cicc
    @0
    @14
    cA
    fveq2
    #
    @21
    oveq12d
    cbvixpv
    eleq2i
    biimpi
    ad2antlr
    @7
    @15
    simpr
    wph
    @19
    wa
    @15
    wa
    #
    @20
    @16
    @22
    @20
    @22
    @17
    cr
    @20
    @22
    @16
    @16
    wph
    @15
    @16
    cr
    wcel
    @19
    wph
    cX
    cr
    @14
    cA
    wph
    @12
    cX
    cr
    cA
    wf
    rrxsnicc.1
    cA
    cr
    cX
    elmapi
    syl
    #
    ffvelrnda
    adantlr
    #
    @24
    iccssred
    @19
    @15
    @20
    @17
    wcel
    #
    wph
    vj
    cX
    @17
    @5
    fvixp2
    adantll
    #
    sseldd
    rexrd
    @22
    @16
    @24
    rexrd
    #
    @22
    @16
    cxr
    wcel
    #
    @28
    @25
    @20
    @16
    cle
    wbr
    @27
    @27
    @26
    @16
    @16
    @20
    iccleub
    syl3anc
    @22
    @28
    @28
    @25
    @16
    @20
    cle
    wbr
    @27
    @27
    @26
    @16
    @16
    @20
    iccgelb
    syl3anc
    xrletrid
    syl21anc
    eqfnfvd
    @8
    @9
    @9
    @8
    vf
    cA
    velsn
    bicomi
    biimpi
    syl
    ssd
    wph
    cA
    @3
    wcel
    #
    @4
    @3
    wss
    #
    wph
    cA
    cvv
    wcel
    #
    @10
    @1
    @2
    wcel
    #
    vk
    cX
    wral
    #
    w3a
    @29
    wph
    @31
    @10
    @33
    wph
    cA
    @11
    rrxsnicc.1
    elexd
    @13
    wph
    @32
    vk
    cX
    wph
    @0
    cX
    wcel
    wa
    #
    @1
    @1
    @1
    wph
    cX
    cr
    @0
    cA
    @23
    ffvelrnda
    #
    @35
    @35
    @34
    @1
    @35
    leidd
    #
    @36
    eliccd
    ralrimiva
    3jca
    vk
    cX
    @2
    cA
    elixp2
    sylibr
    wph
    @12
    @29
    @30
    wb
    rrxsnicc.1
    cA
    @3
    @11
    snssg
    syl
    mpbid
    eqssd
end
