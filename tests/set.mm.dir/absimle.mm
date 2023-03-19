include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "cim.mm"
include "cle.mm"
include "wbr.mm"
include "negicn.mm"
include "a1i.mm"
include "id.mm"
include "mulcld.mm"
include "absrele.mm"
include "syl.mm"
include "imre.mm"
include "fveq2d.mm"
include "wceq.mm"
include "absmul.mm"
include "mpan.mm"
include "c1.mm"
include "ax-icn.mm"
include "absneg.mm"
include "ax-mp.mm"
include "absi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "abscl.mm"
include "recnd.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"

theorem absimle
  let cA: class A


  assert |- ( A e. CC -> ( abs ` ( Im ` A ) ) <_ ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    cre
    cfv
    #
    cabs
    cfv
    #
    @2
    cabs
    cfv
    #
    cA
    cim
    cfv
    #
    cabs
    cfv
    cA
    cabs
    cfv
    #
    cle
    @0
    @2
    cc
    wcel
    @4
    @5
    cle
    wbr
    @0
    @1
    cA
    @1
    cc
    wcel
    #
    @0
    negicn
    a1i
    @0
    id
    mulcld
    @2
    absrele
    syl
    @0
    @6
    @3
    cabs
    cA
    imre
    fveq2d
    @0
    @5
    @1
    cabs
    cfv
    #
    @7
    cmul
    co
    #
    @7
    @8
    @0
    @5
    @10
    wceq
    negicn
    @1
    cA
    absmul
    mpan
    @0
    @10
    c1
    @7
    cmul
    co
    @7
    @9
    c1
    @7
    cmul
    @9
    ci
    cabs
    cfv
    #
    c1
    ci
    cc
    wcel
    @9
    @11
    wceq
    ax-icn
    ci
    absneg
    ax-mp
    absi
    eqtri
    oveq1i
    @0
    @7
    @0
    @7
    cA
    abscl
    recnd
    mulid2d
    syl5eq
    eqtr2d
    3brtr4d
end
