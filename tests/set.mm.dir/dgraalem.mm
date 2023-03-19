include "caa.mm"
include "wcel.mm"
include "cdgraa.mm"
include "cfv.mm"
include "cv.mm"
include "cdgr.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "dgraaval.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "cc.mm"
include "wi.mm"
include "eldifsn.mm"
include "biimpi.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "dgrnznn.mm"
include "syl12anc.mm"
include "simpll.mm"
include "eqid.mm"
include "jctil.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "rexlimiva.mm"
include "impcom.mm"
include "elqaa.mm"
include "rabn0.mm"
include "3imtr4i.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylib.mm"

theorem dgraalem
  let cA: class A
  let vp: setvar p
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P

  disjoint A p
  disjoint A d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d p
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint P d
  disjoint P p
  disjoint P a
  disjoint P b
  disjoint P c
  assert |- ( A e. AA -> ( ( degAA ` A ) e. NN /\ E. p e. ( ( Poly ` QQ ) \ { 0p } ) ( ( deg ` p ) = ( degAA ` A ) /\ ( p ` A ) = 0 ) ) )

  proof
    cA
    caa
    wcel
    #
    cA
    cdgraa
    cfv
    #
    vp
    cv
    #
    cdgr
    cfv
    #
    va
    cv
    #
    wceq
    #
    cA
    @2
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vp
    cq
    cply
    cfv
    #
    c0p
    csn
    cdif
    #
    wrex
    #
    va
    cn
    crab
    #
    wcel
    @1
    cn
    wcel
    @3
    @1
    wceq
    #
    @7
    wa
    #
    vp
    @10
    wrex
    #
    wa
    @0
    @1
    @12
    cr
    clt
    cinf
    #
    @12
    cA
    vp
    va
    dgraaval
    @0
    @12
    c1
    cuz
    cfv
    #
    wss
    @12
    c0
    wne
    #
    @16
    @12
    wcel
    @12
    cn
    @17
    @11
    va
    cn
    ssrab2
    nnuz
    sseqtri
    cA
    cc
    wcel
    #
    cA
    vb
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vb
    @10
    wrex
    #
    wa
    @11
    va
    cn
    wrex
    #
    @0
    @18
    @23
    @19
    @24
    @22
    @19
    @24
    wi
    vb
    @10
    @20
    @10
    wcel
    #
    @22
    wa
    #
    @19
    @24
    @26
    @19
    wa
    #
    @20
    cdgr
    cfv
    #
    cn
    wcel
    #
    @25
    @28
    @28
    wceq
    #
    @22
    wa
    #
    @24
    @27
    @20
    @9
    wcel
    @20
    c0p
    wne
    wa
    #
    @19
    @22
    @29
    @25
    @32
    @22
    @19
    @25
    @32
    @20
    @9
    c0p
    eldifsn
    biimpi
    ad2antrr
    @26
    @19
    simpr
    @25
    @22
    @19
    simplr
    #
    cA
    @20
    cq
    dgrnznn
    syl12anc
    @25
    @22
    @19
    simpll
    @27
    @22
    @30
    @33
    @28
    eqid
    jctil
    @8
    @31
    @3
    @28
    wceq
    #
    @7
    wa
    va
    vp
    @28
    @20
    cn
    @10
    @4
    @28
    wceq
    @5
    @34
    @7
    @4
    @28
    @3
    eqeq2
    anbi1d
    @2
    @20
    wceq
    #
    @34
    @30
    @7
    @22
    @35
    @3
    @28
    @28
    @2
    @20
    cdgr
    fveq2
    eqeq1d
    @35
    @6
    @21
    cc0
    cA
    @2
    @20
    fveq1
    eqeq1d
    anbi12d
    rspc2ev
    syl3anc
    ex
    rexlimiva
    impcom
    cA
    vb
    elqaa
    @11
    va
    cn
    rabn0
    3imtr4i
    @12
    c1
    infssuzcl
    sylancr
    eqeltrd
    @11
    @15
    va
    @1
    cn
    @4
    @1
    wceq
    #
    @8
    @14
    vp
    @10
    @36
    @5
    @13
    @7
    @4
    @1
    @3
    eqeq2
    anbi1d
    rexbidv
    elrab
    sylib
end
