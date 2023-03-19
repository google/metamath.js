include "wcel.mm"
include "csn.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "fsn2g.mm"
include "simprbda.mm"
include "adantrr.mm"
include "wb.mm"
include "adantl.mm"
include "simprr.mm"
include "rspcedvd.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "wss.mm"
include "wf1o.mm"
include "cvv.mm"
include "vex.mm"
include "f1osng.mm"
include "mpan2.mm"
include "ad3antrrr.mm"
include "f1of.mm"
include "syl.mm"
include "simplr.mm"
include "snssd.mm"
include "fss.mm"
include "syl2anc.mm"
include "fvsng.mm"
include "eqcomd.mm"
include "snex.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "simprl.mm"
include "simpllr.mm"
include "simplrr.mm"
include "mpbid.mm"
include "mpdan.mm"
include "jca.mm"
include "eximdv.mm"
include "mpd.mm"
include "simpr.mm"
include "r19.29af.mm"
include "impbida.mm"

theorem fsnex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vf: setvar f
  let cV: class V
  assume fsnex.1: |- ( x = ( f ` A ) -> ( ps <-> ph ) )

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint D f
  disjoint D x
  disjoint V f
  disjoint V x
  disjoint f ps
  disjoint ph x
  assert |- ( A e. V -> ( E. f ( f : { A } --> D /\ ph ) <-> E. x e. D ps ) )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cD
    vf
    cv
    #
    wf
    #
    wph
    wa
    #
    vf
    wex
    #
    wps
    vx
    cD
    wrex
    #
    @0
    @5
    @6
    @0
    @4
    @6
    vf
    @0
    @4
    @6
    @0
    @4
    wa
    #
    wps
    wph
    vx
    cA
    @2
    cfv
    #
    cD
    @0
    @3
    @8
    cD
    wcel
    #
    wph
    @0
    @3
    @9
    @2
    cA
    @8
    cop
    csn
    wceq
    cA
    cD
    @2
    cV
    fsn2g
    simprbda
    adantrr
    vx
    cv
    #
    @8
    wceq
    #
    wps
    wph
    wb
    #
    @7
    fsnex.1
    adantl
    @0
    @3
    wph
    simprr
    rspcedvd
    ex
    exlimdv
    imp
    @0
    @6
    wa
    #
    wps
    @5
    vx
    cD
    @0
    @6
    vx
    @0
    vx
    nfv
    wps
    vx
    cD
    nfre1
    nfan
    @13
    @10
    cD
    wcel
    #
    wa
    #
    wps
    wa
    #
    @3
    @11
    wa
    #
    vf
    wex
    #
    @5
    @16
    @1
    cD
    cA
    @10
    cop
    #
    csn
    #
    wf
    #
    @10
    cA
    @20
    cfv
    #
    wceq
    #
    @18
    @16
    @1
    @10
    csn
    #
    @20
    wf
    #
    @24
    cD
    wss
    @21
    @16
    @1
    @24
    @20
    wf1o
    #
    @25
    @0
    @26
    @6
    @14
    wps
    @0
    @10
    cvv
    wcel
    #
    @26
    vx
    vex
    #
    cA
    @10
    cV
    cvv
    f1osng
    mpan2
    ad3antrrr
    @1
    @24
    @20
    f1of
    syl
    @16
    @10
    cD
    @13
    @14
    wps
    simplr
    snssd
    @1
    @24
    cD
    @20
    fss
    syl2anc
    @0
    @23
    @6
    @14
    wps
    @0
    @22
    @10
    @0
    @27
    @22
    @10
    wceq
    @28
    cA
    @10
    cV
    cvv
    fvsng
    mpan2
    eqcomd
    ad3antrrr
    @17
    @21
    @23
    wa
    vf
    @20
    @19
    snex
    @2
    @20
    wceq
    #
    @3
    @21
    @11
    @23
    @1
    cD
    @2
    @20
    feq1
    @29
    @8
    @22
    @10
    cA
    @2
    @20
    fveq1
    eqeq2d
    anbi12d
    spcev
    syl2anc
    @16
    @17
    @4
    vf
    @16
    @17
    @4
    @16
    @17
    wa
    #
    @3
    wph
    @16
    @3
    @11
    simprl
    #
    @30
    @3
    wph
    @31
    @30
    @3
    wa
    #
    wps
    wph
    @15
    wps
    @17
    @3
    simpllr
    @32
    @11
    @12
    @16
    @3
    @11
    @3
    simplrr
    fsnex.1
    syl
    mpbid
    mpdan
    jca
    ex
    eximdv
    mpd
    @0
    @6
    simpr
    r19.29af
    impbida
end
