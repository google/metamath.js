include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "simpl.mm"
include "recnd.mm"
include "gt0ne0.mm"
include "recne0d.mm"
include "necomd.mm"
include "neneqd.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "cneg.mm"
include "cmul.mm"
include "simpll.mm"
include "wne.mm"
include "adantr.mm"
include "rereccld.mm"
include "renegcld.mm"
include "simpr.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "simplr.mm"
include "mulgt0d.mm"
include "cc.mm"
include "reccld.mm"
include "mulneg1d.mm"
include "recid2d.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "1red.mm"
include "mpbird.mm"
include "ex.mm"
include "mtoi.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "wb.mm"
include "axlttri.mm"
include "sylancr.mm"

theorem recgt0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> 0 < ( 1 / A ) )

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
    cc0
    c1
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    cc0
    @3
    wceq
    #
    @3
    cc0
    clt
    wbr
    #
    wo
    wn
    #
    @2
    @5
    wn
    @6
    wn
    @7
    @2
    cc0
    @3
    @2
    @3
    cc0
    @2
    cA
    @2
    cA
    @0
    @1
    simpl
    #
    recnd
    #
    cA
    gt0ne0
    #
    recne0d
    necomd
    neneqd
    @2
    @6
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    clt
    wbr
    @11
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    ax-mp
    @2
    @6
    @11
    @2
    @6
    wa
    #
    @11
    cc0
    c1
    cneg
    #
    clt
    wbr
    @12
    cc0
    @3
    cneg
    #
    cA
    cmul
    co
    #
    @13
    clt
    @12
    @14
    cA
    @12
    @3
    @12
    cA
    @0
    @1
    @6
    simpll
    #
    @2
    cA
    cc0
    wne
    @6
    @10
    adantr
    #
    rereccld
    renegcld
    @16
    @12
    @6
    cc0
    @14
    clt
    wbr
    @2
    @6
    simpr
    @12
    @3
    @2
    @3
    cr
    wcel
    #
    @6
    @2
    cA
    @8
    @10
    rereccld
    #
    adantr
    lt0neg1d
    mpbid
    @0
    @1
    @6
    simplr
    mulgt0d
    @12
    @15
    @3
    cA
    cmul
    co
    #
    cneg
    @13
    @12
    @3
    cA
    @12
    cA
    @2
    cA
    cc
    wcel
    @6
    @9
    adantr
    #
    @17
    reccld
    @21
    mulneg1d
    @12
    @20
    c1
    @12
    cA
    @21
    @17
    recid2d
    negeqd
    eqtrd
    breqtrd
    @12
    c1
    @12
    1red
    lt0neg1d
    mpbird
    ex
    mtoi
    @5
    @6
    ioran
    sylanbrc
    @2
    cc0
    cr
    wcel
    @18
    @4
    @7
    wb
    0re
    @19
    cc0
    @3
    axlttri
    sylancr
    mpbird
end
