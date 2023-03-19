include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cim.mm"
include "caddc.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "imcl.mm"
include "sqge0d.mm"
include "recl.mm"
include "resqcld.mm"
include "addge01d.mm"
include "mpbid.mm"
include "cr.mm"
include "wb.mm"
include "readdcld.mm"
include "addge0d.mm"
include "sqrtle.mm"
include "syl22anc.mm"
include "wceq.mm"
include "absre.mm"
include "syl.mm"
include "absval2.mm"
include "3brtr4d.mm"

theorem absrele
  let cA: class A


  assert |- ( A e. CC -> ( abs ` ( Re ` A ) ) <_ ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @2
    cA
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    @1
    cabs
    cfv
    #
    cA
    cabs
    cfv
    cle
    @0
    @2
    @6
    cle
    wbr
    #
    @3
    @7
    cle
    wbr
    #
    @0
    cc0
    @5
    cle
    wbr
    @9
    @0
    @4
    cA
    imcl
    #
    sqge0d
    #
    @0
    @2
    @5
    @0
    @1
    cA
    recl
    #
    resqcld
    #
    @0
    @4
    @11
    resqcld
    #
    addge01d
    mpbid
    @0
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @9
    @10
    wb
    @14
    @0
    @1
    @13
    sqge0d
    #
    @0
    @2
    @5
    @14
    @15
    readdcld
    @0
    @2
    @5
    @14
    @15
    @16
    @12
    addge0d
    @2
    @6
    sqrtle
    syl22anc
    mpbid
    @0
    @1
    cr
    wcel
    @8
    @3
    wceq
    @13
    @1
    absre
    syl
    cA
    absval2
    3brtr4d
end
