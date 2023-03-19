include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "1re.mm"
include "a1i.mm"
include "simp1.mm"
include "cn0.mm"
include "simp2.mm"
include "nnnn0d.mm"
include "reexpcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "cmul.mm"
include "cmin.mm"
include "cle.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "wi.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "expge1.mm"
include "syl3anc.mm"
include "cc0.mm"
include "wb.mm"
include "0red.mm"
include "0lt1.mm"
include "lttrd.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "mulid2d.mm"
include "eqcomd.mm"
include "wceq.mm"
include "expm1t.mm"
include "3brtr4d.mm"
include "ltletrd.mm"

theorem expgt1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN /\ 1 < A ) -> 1 < ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    w3a
    #
    c1
    cA
    cA
    cN
    cexp
    co
    #
    c1
    cr
    wcel
    #
    @3
    1re
    a1i
    #
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    cN
    cn0
    wcel
    @4
    cr
    wcel
    @7
    @3
    cN
    @0
    @1
    @2
    simp2
    #
    nnnn0d
    cA
    cN
    reexpcl
    syl2anc
    @0
    @1
    @2
    simp3
    #
    @3
    c1
    cA
    cmul
    co
    #
    cA
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cA
    cmul
    co
    #
    cA
    @4
    cle
    @3
    c1
    @12
    cle
    wbr
    #
    @10
    @13
    cle
    wbr
    #
    @3
    @0
    @11
    cn0
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    @14
    @7
    @3
    @1
    @16
    @8
    cN
    nnm1nn0
    syl
    #
    @3
    @2
    @17
    @9
    @3
    @5
    @0
    @2
    @17
    wi
    1re
    @7
    c1
    cA
    ltle
    sylancr
    mpd
    cA
    @11
    expge1
    syl3anc
    @3
    @5
    @12
    cr
    wcel
    #
    @0
    cc0
    cA
    clt
    wbr
    @14
    @15
    wb
    @6
    @3
    @0
    @16
    @19
    @7
    @18
    cA
    @11
    reexpcl
    syl2anc
    @7
    @3
    cc0
    c1
    cA
    @3
    0red
    @6
    @7
    cc0
    c1
    clt
    wbr
    @3
    0lt1
    a1i
    @9
    lttrd
    c1
    @12
    cA
    lemul1
    syl112anc
    mpbid
    @3
    @10
    cA
    @3
    cA
    @0
    @1
    cA
    cc
    wcel
    #
    @2
    cA
    recn
    3ad2ant1
    #
    mulid2d
    eqcomd
    @3
    @20
    @1
    @4
    @13
    wceq
    @21
    @8
    cA
    cN
    expm1t
    syl2anc
    3brtr4d
    ltletrd
end
