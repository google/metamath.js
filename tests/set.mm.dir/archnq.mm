include "cnq.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c1o.mm"
include "cpli.mm"
include "co.mm"
include "cnpi.mm"
include "cop.mm"
include "cltq.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cxp.mm"
include "elpqn.mm"
include "xp1st.mm"
include "syl.mm"
include "1pi.mm"
include "addclpi.mm"
include "sylancl.mm"
include "c2nd.mm"
include "cmi.mm"
include "clti.mm"
include "wn.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "ltexpi.mm"
include "mpbiri.mm"
include "nlt1pi.mm"
include "wb.mm"
include "ltmpi.mm"
include "mulidpi.mm"
include "breq2d.mm"
include "bitrd.mm"
include "mtbii.mm"
include "ltsopi.mm"
include "ltrelpi.mm"
include "sotri3.mm"
include "syl3anc.mm"
include "pinq.mm"
include "ordpinq.mm"
include "mpdan.mm"
include "ovex.mm"
include "elexi.mm"
include "op2nd.mm"
include "oveq2i.mm"
include "syl5eq.mm"
include "op1st.mm"
include "oveq1i.mm"
include "a1i.mm"
include "breq12d.mm"
include "mpbird.mm"
include "opeq1.mm"

theorem archnq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Q. -> E. x e. N. A <Q <. x , 1o >. )

  proof
    cA
    cnq
    wcel
    #
    cA
    c1st
    cfv
    #
    c1o
    cpli
    co
    #
    cnpi
    wcel
    #
    cA
    @2
    c1o
    cop
    #
    cltq
    wbr
    #
    cA
    vx
    cv
    #
    c1o
    cop
    #
    cltq
    wbr
    #
    vx
    cnpi
    wrex
    @0
    @1
    cnpi
    wcel
    #
    c1o
    cnpi
    wcel
    #
    @3
    @0
    cA
    cnpi
    cnpi
    cxp
    wcel
    #
    @9
    cA
    elpqn
    #
    cA
    cnpi
    cnpi
    xp1st
    syl
    #
    1pi
    @1
    c1o
    addclpi
    sylancl
    #
    @0
    @5
    @1
    @2
    cA
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    @0
    @16
    cnpi
    wcel
    #
    @1
    @2
    clti
    wbr
    #
    @16
    @2
    clti
    wbr
    #
    wn
    @17
    @0
    @3
    @15
    cnpi
    wcel
    #
    @18
    @14
    @0
    @11
    @21
    @12
    cA
    cnpi
    cnpi
    xp2nd
    syl
    @2
    @15
    mulclpi
    syl2anc
    @0
    @9
    @3
    @19
    @13
    @14
    @9
    @3
    wa
    @19
    @1
    @6
    cpli
    co
    #
    @2
    wceq
    #
    vx
    cnpi
    wrex
    #
    @10
    @2
    @2
    wceq
    #
    @24
    1pi
    @2
    eqid
    @23
    @25
    vx
    c1o
    cnpi
    @6
    c1o
    wceq
    @22
    @2
    @2
    @6
    c1o
    @1
    cpli
    oveq2
    eqeq1d
    rspcev
    mp2an
    vx
    @1
    @2
    ltexpi
    mpbiri
    syl2anc
    @0
    @15
    c1o
    clti
    wbr
    #
    @20
    @15
    nlt1pi
    @0
    @26
    @16
    @2
    c1o
    cmi
    co
    #
    clti
    wbr
    #
    @20
    @0
    @3
    @26
    @28
    wb
    @14
    @15
    c1o
    @2
    ltmpi
    syl
    @0
    @27
    @2
    @16
    clti
    @0
    @3
    @27
    @2
    wceq
    @14
    @2
    mulidpi
    syl
    breq2d
    bitrd
    mtbii
    @1
    @2
    @16
    clti
    cnpi
    ltsopi
    ltrelpi
    sotri3
    syl3anc
    @0
    @5
    @1
    @4
    c2nd
    cfv
    #
    cmi
    co
    #
    @4
    c1st
    cfv
    #
    @15
    cmi
    co
    #
    clti
    wbr
    #
    @17
    @0
    @4
    cnq
    wcel
    #
    @5
    @33
    wb
    @0
    @3
    @34
    @14
    @2
    pinq
    syl
    cA
    @4
    ordpinq
    mpdan
    @0
    @30
    @1
    @32
    @16
    clti
    @0
    @30
    @1
    c1o
    cmi
    co
    #
    @1
    @29
    c1o
    @1
    cmi
    @2
    c1o
    @1
    c1o
    cpli
    ovex
    #
    c1o
    cnpi
    1pi
    elexi
    #
    op2nd
    oveq2i
    @0
    @9
    @35
    @1
    wceq
    @13
    @1
    mulidpi
    syl
    syl5eq
    @32
    @16
    wceq
    @0
    @31
    @2
    @15
    cmi
    @2
    c1o
    @36
    @37
    op1st
    oveq1i
    a1i
    breq12d
    bitrd
    mpbird
    @8
    @5
    vx
    @2
    cnpi
    @6
    @2
    wceq
    @7
    @4
    cA
    cltq
    @6
    @2
    c1o
    opeq1
    breq2d
    rspcev
    syl2anc
end
