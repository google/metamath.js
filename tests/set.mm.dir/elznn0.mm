include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "cneg.mm"
include "w3o.mm"
include "wa.mm"
include "cn0.mm"
include "wo.mm"
include "elz.mm"
include "wb.mm"
include "elnn0.mm"
include "a1i.mm"
include "cc.mm"
include "recn.mm"
include "0cn.mm"
include "negcon1.mm"
include "sylancl.mm"
include "neg0.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "orbi12d.mm"
include "3orass.mm"
include "orcom.mm"
include "orordir.mm"
include "3bitrri.mm"
include "syl6rbb.mm"
include "pm5.32i.mm"

theorem elznn0
  let cN: class N


  assert |- ( N e. ZZ <-> ( N e. RR /\ ( N e. NN0 \/ -u N e. NN0 ) ) )

  proof
    cN
    cz
    wcel
    cN
    cr
    wcel
    #
    cN
    cc0
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    w3o
    #
    wa
    @0
    cN
    cn0
    wcel
    #
    @3
    cn0
    wcel
    #
    wo
    #
    wa
    cN
    elz
    @0
    @5
    @8
    @0
    @8
    @2
    @1
    wo
    #
    @4
    @1
    wo
    #
    wo
    #
    @5
    @0
    @6
    @9
    @7
    @10
    @6
    @9
    wb
    @0
    cN
    elnn0
    a1i
    @7
    @4
    @3
    cc0
    wceq
    #
    wo
    @0
    @10
    @3
    elnn0
    @0
    @12
    @1
    @4
    @0
    @12
    cc0
    cneg
    #
    cN
    wceq
    #
    @1
    @0
    cN
    cc
    wcel
    cc0
    cc
    wcel
    @12
    @14
    wb
    cN
    recn
    0cn
    cN
    cc0
    negcon1
    sylancl
    @14
    cc0
    cN
    wceq
    @1
    @13
    cc0
    cN
    neg0
    eqeq1i
    cc0
    cN
    eqcom
    bitri
    syl6bb
    orbi2d
    syl5bb
    orbi12d
    @5
    @1
    @2
    @4
    wo
    #
    wo
    @15
    @1
    wo
    @11
    @1
    @2
    @4
    3orass
    @1
    @15
    orcom
    @2
    @4
    @1
    orordir
    3bitrri
    syl6rbb
    pm5.32i
    bitri
end
