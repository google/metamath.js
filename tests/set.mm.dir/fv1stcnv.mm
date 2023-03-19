include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "snidg.mm"
include "anim2i.mm"
include "eqid.mm"
include "jctil.mm"
include "wb.mm"
include "cvv.mm"
include "opex.mm"
include "brcnvg.mm"
include "mpan2.mm"
include "brresg.mm"
include "bitrd.mm"
include "adantr.mm"
include "opelxp.mm"
include "anbi2i.mm"
include "br1steqg.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "wfn.mm"
include "wf1o.mm"
include "1stconst.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "simpl.mm"
include "fnbrfvb.mm"
include "syl2an2.mm"

theorem fv1stcnv
  let cA: class A
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. A /\ Y e. V ) -> ( `' ( 1st |` ( A X. { Y } ) ) ` X ) = <. X , Y >. )

  proof
    cX
    cA
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    c1st
    cA
    cY
    csn
    #
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
    cX
    @7
    @6
    wbr
    #
    @2
    @9
    cX
    cX
    wceq
    #
    @0
    cY
    @3
    wcel
    #
    wa
    #
    wa
    #
    @2
    @12
    @10
    @1
    @11
    @0
    cY
    cV
    snidg
    anim2i
    cX
    eqid
    jctil
    @2
    @9
    @7
    cX
    c1st
    wbr
    #
    @7
    @4
    wcel
    #
    wa
    #
    @13
    @0
    @9
    @16
    wb
    @1
    @0
    @9
    @7
    cX
    @5
    wbr
    #
    @16
    @0
    @7
    cvv
    wcel
    @9
    @17
    wb
    cX
    cY
    opex
    cX
    @7
    cA
    cvv
    @5
    brcnvg
    mpan2
    @7
    cX
    c1st
    @4
    cA
    brresg
    bitrd
    adantr
    @16
    @14
    @12
    wa
    @2
    @13
    @15
    @12
    @14
    cX
    cY
    cA
    @3
    opelxp
    anbi2i
    @2
    @14
    @10
    @12
    cX
    cY
    cX
    cA
    cV
    br1steqg
    anbi1d
    syl5bb
    bitrd
    mpbird
    @1
    @6
    cA
    wfn
    #
    @0
    @0
    @8
    @9
    wb
    @1
    @4
    cA
    @5
    wf1o
    cA
    @4
    @6
    wf1o
    @18
    cA
    cY
    cV
    1stconst
    @4
    cA
    @5
    f1ocnv
    cA
    @4
    @6
    f1ofn
    3syl
    @0
    @1
    simpl
    cA
    cX
    @7
    @6
    fnbrfvb
    syl2an2
    mpbird
end
