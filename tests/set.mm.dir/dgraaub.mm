include "cq.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgraa.mm"
include "cv.mm"
include "cdgr.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "caa.mm"
include "simprl.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantr.mm"
include "simprr.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "elqaa.mm"
include "sylanbrc.mm"
include "dgraaval.mm"
include "syl.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "wbr.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "dgrnznn.mm"
include "eqid.mm"
include "jctil.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "infssuzle.mm"
include "sylancr.mm"
include "eqbrtrd.mm"

theorem dgraaub
  let cA: class A
  let cP: class P
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( P e. ( Poly ` QQ ) /\ P =/= 0p ) /\ ( A e. CC /\ ( P ` A ) = 0 ) ) -> ( degAA ` A ) <_ ( deg ` P ) )

  proof
    cP
    cq
    cply
    cfv
    #
    wcel
    cP
    c0p
    wne
    wa
    #
    cA
    cc
    wcel
    #
    cA
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wa
    #
    cA
    cdgraa
    cfv
    #
    vb
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
    @8
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vb
    @0
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
    cr
    clt
    cinf
    #
    cP
    cdgr
    cfv
    #
    cle
    @6
    cA
    caa
    wcel
    #
    @7
    @18
    wceq
    @6
    @2
    cA
    @10
    cfv
    #
    cc0
    wceq
    #
    va
    @15
    wrex
    #
    @20
    @1
    @2
    @4
    simprl
    @6
    cP
    @15
    wcel
    #
    @4
    @23
    @1
    @24
    @5
    @24
    @1
    cP
    @0
    c0p
    eldifsn
    biimpri
    adantr
    #
    @1
    @2
    @4
    simprr
    #
    @22
    @4
    va
    cP
    @15
    @10
    cP
    wceq
    @21
    @3
    cc0
    cA
    @10
    cP
    fveq1
    eqeq1d
    rspcev
    syl2anc
    cA
    va
    elqaa
    sylanbrc
    cA
    vb
    va
    dgraaval
    syl
    @6
    @17
    c1
    cuz
    cfv
    #
    wss
    @19
    @17
    wcel
    #
    @18
    @19
    cle
    wbr
    @17
    cn
    @27
    @16
    va
    cn
    ssrab2
    nnuz
    sseqtri
    @6
    @19
    cn
    wcel
    @9
    @19
    wceq
    #
    @13
    wa
    #
    vb
    @15
    wrex
    #
    @28
    cA
    cP
    cq
    dgrnznn
    @6
    @24
    @19
    @19
    wceq
    #
    @4
    wa
    #
    @31
    @25
    @6
    @4
    @32
    @26
    @19
    eqid
    jctil
    @30
    @33
    vb
    cP
    @15
    @8
    cP
    wceq
    #
    @29
    @32
    @13
    @4
    @34
    @9
    @19
    @19
    @8
    cP
    cdgr
    fveq2
    eqeq1d
    @34
    @12
    @3
    cc0
    cA
    @8
    cP
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl2anc
    @16
    @31
    va
    @19
    cn
    @10
    @19
    wceq
    #
    @14
    @30
    vb
    @15
    @35
    @11
    @29
    @13
    @10
    @19
    @9
    eqeq2
    anbi1d
    rexbidv
    elrab
    sylanbrc
    @19
    @17
    c1
    infssuzle
    sylancr
    eqbrtrd
end
