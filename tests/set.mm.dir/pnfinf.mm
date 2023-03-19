include "crp.mm"
include "wcel.mm"
include "cpnf.mm"
include "cxrs.mm"
include "cinftm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "clt.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "cn.mm"
include "wral.mm"
include "rpgt0.mm"
include "wa.mm"
include "cr.mm"
include "cxmu.mm"
include "cz.mm"
include "cxr.mm"
include "wceq.mm"
include "nnz.mm"
include "adantl.mm"
include "rpxr.mm"
include "adantr.mm"
include "xrsmulgzz.mm"
include "syl2anc.mm"
include "zred.mm"
include "rpre.mm"
include "cmul.mm"
include "rexmul.mm"
include "remulcl.mm"
include "eqeltrd.mm"
include "ltpnf.mm"
include "syl.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cvv.mm"
include "xrsex.mm"
include "pnfxr.mm"
include "xrsbas.mm"
include "xrs0.mm"
include "eqid.mm"
include "xrslt.mm"
include "isinftm.mm"
include "mp3an13.mm"
include "mpbir2and.mm"

theorem pnfinf
  let cA: class A
  let vn: setvar n


  assert |- ( A e. RR+ -> A ( <<< ` RR*s ) +oo )

  proof
    cA
    crp
    wcel
    #
    cA
    cpnf
    cxrs
    cinftm
    cfv
    wbr
    #
    cc0
    cA
    clt
    wbr
    #
    vn
    cv
    #
    cA
    cxrs
    cmg
    cfv
    #
    co
    #
    cpnf
    clt
    wbr
    #
    vn
    cn
    wral
    #
    cA
    rpgt0
    @0
    @6
    vn
    cn
    @0
    @3
    cn
    wcel
    #
    wa
    #
    @5
    cr
    wcel
    @6
    @9
    @5
    @3
    cA
    cxmu
    co
    #
    cr
    @9
    @3
    cz
    wcel
    #
    cA
    cxr
    wcel
    #
    @5
    @10
    wceq
    @8
    @11
    @0
    @3
    nnz
    adantl
    #
    @0
    @12
    @8
    cA
    rpxr
    #
    adantr
    @3
    cA
    xrsmulgzz
    syl2anc
    @9
    @3
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @10
    cr
    wcel
    @9
    @3
    @13
    zred
    @0
    @16
    @8
    cA
    rpre
    adantr
    @15
    @16
    wa
    @10
    @3
    cA
    cmul
    co
    cr
    @3
    cA
    rexmul
    @3
    cA
    remulcl
    eqeltrd
    syl2anc
    eqeltrd
    @5
    ltpnf
    syl
    ralrimiva
    @0
    @12
    @1
    @2
    @7
    wa
    wb
    #
    @14
    cxrs
    cvv
    wcel
    @12
    cpnf
    cxr
    wcel
    @17
    xrsex
    pnfxr
    cxr
    clt
    @4
    vn
    cvv
    cxrs
    cA
    cpnf
    cc0
    xrsbas
    xrs0
    @4
    eqid
    xrslt
    isinftm
    mp3an13
    syl
    mpbir2and
end
