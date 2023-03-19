include "ccat.mm"
include "wcel.mm"
include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "cbs.mm"
include "ciso.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cicfval.mm"
include "breqd.mm"
include "cop.mm"
include "cxp.mm"
include "wne.mm"
include "wa.mm"
include "wfn.mm"
include "cvv.mm"
include "wb.mm"
include "isofn.mm"
include "fvex.mm"
include "sqxpexg.mm"
include "mp1i.mm"
include "0ex.mm"
include "a1i.mm"
include "w3a.mm"
include "df-br.mm"
include "elsuppfn.mm"
include "syl5bb.mm"
include "syl3anc.mm"
include "opelxp1.mm"
include "adantr.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "imp.mm"

theorem ciclcl
  let cC: class C
  let cR: class R
  let cS: class S


  assert |- ( ( C e. Cat /\ R ( ~=c ` C ) S ) -> R e. ( Base ` C ) )

  proof
    cC
    ccat
    wcel
    #
    cR
    cS
    cC
    ccic
    cfv
    #
    wbr
    #
    cR
    cC
    cbs
    cfv
    #
    wcel
    #
    @0
    @2
    cR
    cS
    cC
    ciso
    cfv
    #
    c0
    csupp
    co
    #
    wbr
    #
    @4
    @0
    @1
    @6
    cR
    cS
    cC
    cicfval
    breqd
    @0
    @7
    cR
    cS
    cop
    #
    @3
    @3
    cxp
    #
    wcel
    #
    @8
    @5
    cfv
    c0
    wne
    #
    wa
    #
    @4
    @0
    @5
    @9
    wfn
    #
    @9
    cvv
    wcel
    #
    c0
    cvv
    wcel
    #
    @7
    @12
    wb
    cC
    isofn
    @3
    cvv
    wcel
    @14
    @0
    cC
    cbs
    fvex
    @3
    cvv
    sqxpexg
    mp1i
    @15
    @0
    0ex
    a1i
    @7
    @8
    @6
    wcel
    @13
    @14
    @15
    w3a
    @12
    cR
    cS
    @6
    df-br
    @8
    @5
    cvv
    cvv
    @9
    c0
    elsuppfn
    syl5bb
    syl3anc
    @10
    @4
    @11
    cR
    cS
    @3
    @3
    opelxp1
    adantr
    syl6bi
    sylbid
    imp
end
