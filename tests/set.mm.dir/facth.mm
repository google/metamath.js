include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cquot.mm"
include "co.mm"
include "cmul.mm"
include "cof.mm"
include "cmin.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "plyrem.mm"
include "3adant3.mm"
include "simp3.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"
include "cvv.mm"
include "wf.mm"
include "wb.mm"
include "cnex.mm"
include "a1i.mm"
include "simp1.mm"
include "plyf.mm"
include "syl.mm"
include "cdgr.mm"
include "c1.mm"
include "ccnv.mm"
include "cima.mm"
include "plyremlem.mm"
include "3ad2ant2.mm"
include "simp1d.mm"
include "c0p.mm"
include "wne.mm"
include "plyssc.mm"
include "sseldi.mm"
include "simp2d.mm"
include "ax-1ne0.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "quotcl2.mm"
include "syl3anc.mm"
include "plymulcl.mm"
include "syl2anc.mm"
include "ofsubeq0.mm"
include "mpbid.mm"

theorem facth
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  assume facth.1: |- G = ( Xp oF - ( CC X. { A } ) )


  assert |- ( ( F e. ( Poly ` S ) /\ A e. CC /\ ( F ` A ) = 0 ) -> F = ( G oF x. ( F quot G ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    cF
    cfv
    #
    cc0
    wceq
    #
    w3a
    #
    cF
    cG
    cF
    cG
    cquot
    co
    #
    cmul
    cof
    co
    #
    cmin
    cof
    co
    #
    cc
    cc0
    csn
    #
    cxp
    #
    wceq
    #
    cF
    @7
    wceq
    #
    @5
    @8
    cc
    @3
    csn
    #
    cxp
    #
    @10
    @1
    @2
    @8
    @14
    wceq
    @4
    cA
    @8
    cS
    cF
    cG
    facth.1
    @8
    eqid
    plyrem
    3adant3
    @5
    @13
    @9
    cc
    @5
    @3
    cc0
    @1
    @2
    @4
    simp3
    sneqd
    xpeq2d
    eqtrd
    @5
    cc
    cvv
    wcel
    #
    cc
    cc
    cF
    wf
    #
    cc
    cc
    @7
    wf
    #
    @11
    @12
    wb
    @15
    @5
    cnex
    a1i
    @5
    @1
    @16
    @1
    @2
    @4
    simp1
    #
    cS
    cF
    plyf
    syl
    @5
    @7
    cc
    cply
    cfv
    #
    wcel
    #
    @17
    @5
    cG
    @19
    wcel
    #
    @6
    @19
    wcel
    #
    @20
    @5
    @21
    cG
    cdgr
    cfv
    #
    c1
    wceq
    #
    cG
    ccnv
    @9
    cima
    cA
    csn
    wceq
    #
    @2
    @1
    @21
    @24
    @25
    w3a
    @4
    cA
    cG
    facth.1
    plyremlem
    3ad2ant2
    #
    simp1d
    #
    @5
    cF
    @19
    wcel
    @21
    cG
    c0p
    wne
    #
    @22
    @5
    @0
    @19
    cF
    cS
    plyssc
    @18
    sseldi
    @27
    @5
    @23
    cc0
    wne
    @28
    @5
    @23
    c1
    cc0
    @5
    @21
    @24
    @25
    @26
    simp2d
    c1
    cc0
    wne
    @5
    ax-1ne0
    a1i
    eqnetrd
    cG
    c0p
    @23
    cc0
    cG
    c0p
    wceq
    @23
    c0p
    cdgr
    cfv
    cc0
    cG
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    cc
    cF
    cG
    quotcl2
    syl3anc
    cc
    cG
    @6
    plymulcl
    syl2anc
    cc
    @7
    plyf
    syl
    cc
    cF
    @7
    cvv
    ofsubeq0
    syl3anc
    mpbid
end
