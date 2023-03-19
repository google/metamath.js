include "cpi.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cmin.mm"
include "cr.mm"
include "wb.mm"
include "elioore.mm"
include "caddc.mm"
include "pire.mm"
include "wa.mm"
include "0re.mm"
include "iooshf.mm"
include "mpanr12.mm"
include "mpan2.mm"
include "picn.mm"
include "addid2i.mm"
include "eqcomi.mm"
include "2timesi.mm"
include "oveq12i.mm"
include "eleq2i.mm"
include "syl6rbbr.mm"
include "syl.mm"
include "ibi.mm"
include "sinq12gt0.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "sinmpi.mm"
include "breqtrd.mm"
include "resincld.mm"
include "lt0neg1d.mm"
include "mpbird.mm"

theorem sinq34lt0t
  let cA: class A


  assert |- ( A e. ( _pi (,) ( 2 x. _pi ) ) -> ( sin ` A ) < 0 )

  proof
    cA
    cpi
    c2
    cpi
    cmul
    co
    #
    cioo
    co
    #
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    clt
    wbr
    cc0
    @3
    cneg
    #
    clt
    wbr
    @2
    cc0
    cA
    cpi
    cmin
    co
    #
    csin
    cfv
    #
    @4
    clt
    @2
    @5
    cc0
    cpi
    cioo
    co
    wcel
    #
    cc0
    @6
    clt
    wbr
    @2
    @7
    @2
    cA
    cr
    wcel
    #
    @2
    @7
    wb
    cA
    cpi
    @0
    elioore
    #
    @8
    @7
    cA
    cc0
    cpi
    caddc
    co
    #
    cpi
    cpi
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @2
    @8
    cpi
    cr
    wcel
    #
    @7
    @13
    wb
    #
    pire
    @8
    @14
    wa
    cc0
    cr
    wcel
    @14
    @15
    0re
    pire
    cA
    cpi
    cc0
    cpi
    iooshf
    mpanr12
    mpan2
    @1
    @12
    cA
    cpi
    @10
    @0
    @11
    cioo
    @10
    cpi
    cpi
    picn
    addid2i
    eqcomi
    cpi
    picn
    2timesi
    oveq12i
    eleq2i
    syl6rbbr
    syl
    ibi
    @5
    sinq12gt0
    syl
    @2
    cA
    cc
    wcel
    @6
    @4
    wceq
    @2
    cA
    @9
    recnd
    cA
    sinmpi
    syl
    breqtrd
    @2
    @3
    @2
    cA
    @9
    resincld
    lt0neg1d
    mpbird
end
