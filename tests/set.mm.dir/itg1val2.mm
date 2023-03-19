include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfn.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "cr.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "itg1val.mm"
include "adantr.mm"
include "simpr2.mm"
include "cc.mm"
include "sselda.mm"
include "simpr3.mm"
include "eldifi.mm"
include "syl.mm"
include "i1fima2sn.mm"
include "adantlr.mm"
include "syldan.mm"
include "remulcld.mm"
include "recnd.mm"
include "c0.mm"
include "wf.mm"
include "cin.mm"
include "i1ff.mm"
include "ad2antrr.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "simplr3.mm"
include "ssdifssd.mm"
include "simpr.mm"
include "sseldd.mm"
include "biantrud.mm"
include "eldif.mm"
include "syl6rbbr.mm"
include "mtbid.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fimacnvdisj.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "covol.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovol0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "sylan2.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "simpr1.mm"
include "fsumss.mm"

theorem itg1val2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y

  disjoint F x
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint x y
  disjoint F y
  disjoint A y
  assert |- ( ( F e. dom S.1 /\ ( A e. Fin /\ ( ran F \ { 0 } ) C_ A /\ A C_ ( RR \ { 0 } ) ) ) -> ( S.1 ` F ) = sum_ x e. A ( x x. ( vol ` ( `' F " { x } ) ) ) )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cA
    cfn
    wcel
    #
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    cA
    wss
    #
    cA
    cr
    @3
    cdif
    #
    wss
    #
    w3a
    #
    wa
    #
    cF
    citg1
    cfv
    #
    @4
    vx
    cv
    #
    cF
    ccnv
    @11
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vx
    csu
    #
    cA
    @15
    vx
    csu
    @0
    @10
    @16
    wceq
    @8
    vx
    cF
    itg1val
    adantr
    @9
    @4
    cA
    @15
    vx
    @0
    @1
    @5
    @7
    simpr2
    #
    @9
    @11
    @4
    wcel
    #
    @11
    cA
    wcel
    #
    @15
    cc
    wcel
    @9
    @4
    cA
    @11
    @17
    sselda
    @9
    @19
    wa
    #
    @15
    @20
    @11
    @14
    @20
    @11
    @6
    wcel
    #
    @11
    cr
    wcel
    #
    @9
    cA
    @6
    @11
    @0
    @1
    @5
    @7
    simpr3
    sselda
    #
    @11
    cr
    @3
    eldifi
    syl
    #
    @9
    @19
    @21
    @14
    cr
    wcel
    #
    @23
    @0
    @21
    @25
    @8
    @11
    cr
    cF
    i1fima2sn
    adantlr
    syldan
    remulcld
    recnd
    syldan
    @9
    @11
    cA
    @4
    cdif
    #
    wcel
    #
    wa
    #
    @15
    @11
    cc0
    cmul
    co
    cc0
    @28
    @14
    cc0
    @11
    cmul
    @28
    @14
    c0
    cvol
    cfv
    #
    cc0
    @28
    @13
    c0
    cvol
    @28
    cr
    @2
    cF
    wf
    #
    @2
    @12
    cin
    c0
    wceq
    #
    @13
    c0
    wceq
    @28
    cr
    cr
    cF
    wf
    #
    @30
    @0
    @32
    @8
    @27
    cF
    i1ff
    ad2antrr
    @32
    cF
    cr
    wfn
    @30
    cr
    cr
    cF
    ffn
    cr
    cF
    dffn3
    sylib
    syl
    @28
    @11
    @2
    wcel
    #
    wn
    @31
    @28
    @18
    @33
    @27
    @18
    wn
    @9
    @11
    cA
    @4
    eldifn
    adantl
    @28
    @33
    @33
    @11
    @3
    wcel
    wn
    #
    wa
    @18
    @28
    @34
    @33
    @28
    @21
    @34
    @28
    @26
    @6
    @11
    @28
    cA
    @6
    @4
    @1
    @5
    @7
    @0
    @27
    simplr3
    ssdifssd
    @9
    @27
    simpr
    sseldd
    @11
    cr
    @3
    eldifn
    syl
    biantrud
    @11
    @2
    @3
    eldif
    syl6rbbr
    mtbid
    @2
    @11
    disjsn
    sylibr
    cr
    @2
    @12
    cF
    fimacnvdisj
    syl2anc
    fveq2d
    @29
    c0
    covol
    cfv
    #
    cc0
    c0
    cvol
    cdm
    wcel
    @29
    @35
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    syl6eq
    oveq2d
    @28
    @11
    @28
    @11
    @27
    @9
    @19
    @22
    @11
    cA
    @4
    eldifi
    @24
    sylan2
    recnd
    mul01d
    eqtrd
    @0
    @1
    @5
    @7
    simpr1
    fsumss
    eqtrd
end
