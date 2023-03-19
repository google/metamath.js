include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wa.mm"
include "ccos.mm"
include "caddc.mm"
include "cc0.mm"
include "recoscl.mm"
include "sqge0d.mm"
include "resincl.mm"
include "resqcld.mm"
include "addge01d.mm"
include "mpbid.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "sincossq.mm"
include "syl.mm"
include "sq1.mm"
include "syl6eqr.mm"
include "breqtrd.mm"
include "wb.mm"
include "1re.mm"
include "0le1.mm"
include "lenegsq.mm"
include "mp3an23.mm"
include "lenegcon1.mm"
include "mpan2.mm"
include "anbi2d.mm"
include "bitr3d.mm"
include "ancomd.mm"

theorem sinbnd
  let cA: class A


  assert |- ( A e. RR -> ( -u 1 <_ ( sin ` A ) /\ ( sin ` A ) <_ 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    csin
    cfv
    #
    c1
    cle
    wbr
    #
    c1
    cneg
    @1
    cle
    wbr
    #
    @0
    @1
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @2
    @3
    wa
    #
    @0
    @4
    @4
    cA
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @5
    cle
    @0
    cc0
    @9
    cle
    wbr
    @4
    @10
    cle
    wbr
    @0
    @8
    cA
    recoscl
    #
    sqge0d
    @0
    @4
    @9
    @0
    @1
    cA
    resincl
    #
    resqcld
    @0
    @8
    @11
    resqcld
    addge01d
    mpbid
    @0
    @10
    c1
    @5
    @0
    cA
    cc
    wcel
    @10
    c1
    wceq
    cA
    recn
    cA
    sincossq
    syl
    sq1
    syl6eqr
    breqtrd
    @0
    @1
    cr
    wcel
    #
    @6
    @7
    wb
    @12
    @13
    @2
    @1
    cneg
    c1
    cle
    wbr
    #
    wa
    #
    @6
    @7
    @13
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    @15
    @6
    wb
    1re
    0le1
    @1
    c1
    lenegsq
    mp3an23
    @13
    @14
    @3
    @2
    @13
    @16
    @14
    @3
    wb
    1re
    @1
    c1
    lenegcon1
    mpan2
    anbi2d
    bitr3d
    syl
    mpbid
    ancomd
end
