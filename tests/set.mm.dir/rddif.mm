include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "halfcn.mm"
include "2timesi.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "recn.mm"
include "cc.mm"
include "a1i.mm"
include "nppcan3d.mm"
include "syl5eqr.mm"
include "halfre.mm"
include "readdcl.mm"
include "mpan2.mm"
include "fllep1.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "resubcl.mm"
include "reflcl.mm"
include "1red.mm"
include "leadd1d.mm"
include "mpbird.mm"
include "flle.mm"
include "wa.mm"
include "wb.mm"
include "id.mm"
include "absdifle.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem rddif
  let cA: class A


  assert |- ( A e. RR -> ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) <_ ( 1 / 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cA
    cmin
    co
    cabs
    cfv
    @1
    cle
    wbr
    #
    cA
    @1
    cmin
    co
    #
    @3
    cle
    wbr
    #
    @3
    @2
    cle
    wbr
    #
    @0
    @6
    @5
    c1
    caddc
    co
    #
    @3
    c1
    caddc
    co
    #
    cle
    wbr
    @0
    @8
    @2
    @9
    cle
    @0
    @8
    @5
    @1
    @1
    caddc
    co
    #
    caddc
    co
    @2
    @10
    c1
    @5
    caddc
    c2
    @1
    cmul
    co
    @10
    c1
    @1
    halfcn
    2timesi
    c2
    2cn
    2ne0
    recidi
    eqtr3i
    oveq2i
    @0
    cA
    @1
    @1
    cA
    recn
    @1
    cc
    wcel
    @0
    halfcn
    a1i
    #
    @11
    nppcan3d
    syl5eqr
    @0
    @2
    cr
    wcel
    #
    @2
    @9
    cle
    wbr
    @0
    @1
    cr
    wcel
    #
    @12
    halfre
    cA
    @1
    readdcl
    mpan2
    #
    @2
    fllep1
    syl
    eqbrtrd
    @0
    @5
    @3
    c1
    @0
    @13
    @5
    cr
    wcel
    halfre
    cA
    @1
    resubcl
    mpan2
    @0
    @12
    @3
    cr
    wcel
    #
    @14
    @2
    reflcl
    syl
    #
    @0
    1red
    leadd1d
    mpbird
    @0
    @12
    @7
    @14
    @2
    flle
    syl
    @0
    @15
    @0
    @13
    @4
    @6
    @7
    wa
    wb
    @16
    @0
    id
    @13
    @0
    halfre
    a1i
    @3
    cA
    @1
    absdifle
    syl3anc
    mpbir2and
end
