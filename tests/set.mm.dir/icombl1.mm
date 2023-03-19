include "cr.mm"
include "wcel.mm"
include "csn.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cun.mm"
include "cico.mm"
include "cvol.mm"
include "cdm.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "rexr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ltpnf.mm"
include "snunioo.mm"
include "syl3anc.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "snssi.mm"
include "ovolsn.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "ioombl1.mm"
include "syl.mm"
include "unmbl.mm"
include "eqeltrrd.mm"

theorem icombl1
  let cA: class A


  assert |- ( A e. RR -> ( A [,) +oo ) e. dom vol )

  proof
    cA
    cr
    wcel
    #
    cA
    csn
    #
    cA
    cpnf
    cioo
    co
    #
    cun
    #
    cA
    cpnf
    cico
    co
    #
    cvol
    cdm
    #
    @0
    cA
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cA
    cpnf
    clt
    wbr
    @3
    @4
    wceq
    cA
    rexr
    #
    @7
    @0
    pnfxr
    a1i
    cA
    ltpnf
    cA
    cpnf
    snunioo
    syl3anc
    @0
    @1
    @5
    wcel
    #
    @2
    @5
    wcel
    #
    @3
    @5
    wcel
    @0
    @1
    cr
    wss
    @1
    covol
    cfv
    cc0
    wceq
    @9
    cA
    cr
    snssi
    cA
    ovolsn
    @1
    nulmbl
    syl2anc
    @0
    @6
    @10
    @8
    cA
    ioombl1
    syl
    @1
    @2
    unmbl
    syl2anc
    eqeltrrd
end
