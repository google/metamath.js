include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cn.mm"
include "wrex.mm"
include "simpl.mm"
include "gt0ne0.mm"
include "rereccld.mm"
include "arch.mm"
include "syl.mm"
include "wb.mm"
include "recgt0.mm"
include "jca.mm"
include "nnre.mm"
include "nngt0.mm"
include "ltrec.mm"
include "syl2an.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "recrecd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem nnrecl
  let cA: class A
  let vn: setvar n

  disjoint A n
  assert |- ( ( A e. RR /\ 0 < A ) -> E. n e. NN ( 1 / n ) < A )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    vn
    cv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    c1
    @4
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    vn
    cn
    wrex
    @2
    @3
    cr
    wcel
    #
    @6
    @2
    cA
    @0
    @1
    simpl
    cA
    gt0ne0
    #
    rereccld
    #
    @3
    vn
    arch
    syl
    @2
    @5
    @8
    vn
    cn
    @2
    @4
    cn
    wcel
    #
    wa
    @5
    @7
    c1
    @3
    cdiv
    co
    #
    clt
    wbr
    #
    @8
    @2
    @9
    cc0
    @3
    clt
    wbr
    #
    wa
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    wa
    @5
    @14
    wb
    @12
    @2
    @9
    @15
    @11
    cA
    recgt0
    jca
    @12
    @16
    @17
    @4
    nnre
    @4
    nngt0
    jca
    @3
    @4
    ltrec
    syl2an
    @2
    @14
    @8
    wb
    @12
    @2
    @13
    cA
    @7
    clt
    @2
    cA
    @0
    cA
    cc
    wcel
    @1
    cA
    recn
    adantr
    @10
    recrecd
    breq2d
    adantr
    bitrd
    rexbidva
    mpbid
end
