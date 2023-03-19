include "wcel.mm"
include "wa.mm"
include "c2nd.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "snidg.mm"
include "anim1i.mm"
include "eqid.mm"
include "jctil.mm"
include "wbr.mm"
include "wfn.mm"
include "wb.mm"
include "wf1o.mm"
include "2ndconst.mm"
include "adantr.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "fnbrfvb.mm"
include "sylancom.mm"
include "cvv.mm"
include "opex.mm"
include "brcnvg.mm"
include "mpan2.mm"
include "adantl.mm"
include "brresg.mm"
include "opelxp.mm"
include "anbi2i.mm"
include "br2ndeqg.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem fv2ndcnv
  let cA: class A
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. A ) -> ( `' ( 2nd |` ( { X } X. A ) ) ` Y ) = <. X , Y >. )

  proof
    cX
    cV
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    #
    cY
    c2nd
    cX
    csn
    #
    cA
    cxp
    #
    cres
    #
    ccnv
    #
    cfv
    cX
    cY
    cop
    #
    wceq
    #
    cY
    cY
    wceq
    #
    cX
    @3
    wcel
    #
    @1
    wa
    #
    wa
    #
    @2
    @11
    @9
    @0
    @10
    @1
    cX
    cV
    snidg
    anim1i
    cY
    eqid
    jctil
    @2
    @8
    cY
    @7
    @6
    wbr
    #
    @12
    @0
    @1
    @6
    cA
    wfn
    #
    @8
    @13
    wb
    @2
    @4
    cA
    @5
    wf1o
    #
    cA
    @4
    @6
    wf1o
    @14
    @0
    @15
    @1
    cX
    cA
    cV
    2ndconst
    adantr
    @4
    cA
    @5
    f1ocnv
    cA
    @4
    @6
    f1ofn
    3syl
    cA
    cY
    @7
    @6
    fnbrfvb
    sylancom
    @2
    @13
    @7
    cY
    @5
    wbr
    #
    @12
    @1
    @13
    @16
    wb
    #
    @0
    @1
    @7
    cvv
    wcel
    @17
    cX
    cY
    opex
    cY
    @7
    cA
    cvv
    @5
    brcnvg
    mpan2
    adantl
    @2
    @16
    @7
    cY
    c2nd
    wbr
    #
    @7
    @4
    wcel
    #
    wa
    #
    @12
    @1
    @16
    @20
    wb
    @0
    @7
    cY
    c2nd
    @4
    cA
    brresg
    adantl
    @20
    @18
    @11
    wa
    @2
    @12
    @19
    @11
    @18
    cX
    cY
    @3
    cA
    opelxp
    anbi2i
    @2
    @18
    @9
    @11
    cX
    cY
    cY
    cV
    cA
    br2ndeqg
    anbi1d
    syl5bb
    bitrd
    bitrd
    bitrd
    mpbird
end
