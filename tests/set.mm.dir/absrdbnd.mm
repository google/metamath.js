include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "halfre.mm"
include "readdcl.mm"
include "mpan2.mm"
include "reflcl.mm"
include "syl.mm"
include "recnd.mm"
include "abscl.mm"
include "recn.mm"
include "1re.mm"
include "a1i.mm"
include "resubcld.mm"
include "resubcl.mm"
include "mpancom.mm"
include "abs2dif.mm"
include "syl2anc.mm"
include "rddif.mm"
include "halflt1.mm"
include "ltleii.mm"
include "letrd.mm"
include "subled.mm"
include "cz.mm"
include "wb.mm"
include "cn0.mm"
include "flcld.mm"
include "nn0abscl.mm"
include "nn0zd.mm"
include "peano2zm.mm"
include "flge.mm"
include "mpbid.mm"
include "lesubaddd.mm"

theorem absrdbnd
  let cA: class A


  assert |- ( A e. RR -> ( abs ` ( |_ ` ( A + ( 1 / 2 ) ) ) ) <_ ( ( |_ ` ( abs ` A ) ) + 1 ) )

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
    cabs
    cfv
    #
    c1
    cmin
    co
    #
    cA
    cabs
    cfv
    #
    cfl
    cfv
    #
    cle
    wbr
    #
    @4
    @7
    c1
    caddc
    co
    cle
    wbr
    @0
    @5
    @6
    cle
    wbr
    #
    @8
    @0
    @4
    @6
    c1
    @0
    @3
    cc
    wcel
    #
    @4
    cr
    wcel
    @0
    @3
    @0
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @0
    @1
    cr
    wcel
    #
    @11
    halfre
    cA
    @1
    readdcl
    mpan2
    #
    @2
    reflcl
    syl
    #
    recnd
    #
    @3
    abscl
    syl
    #
    @0
    cA
    cc
    wcel
    #
    @6
    cr
    wcel
    #
    cA
    recn
    #
    cA
    abscl
    syl
    #
    c1
    cr
    wcel
    @0
    1re
    a1i
    #
    @0
    @4
    @6
    cmin
    co
    #
    @3
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    @0
    @4
    @6
    @17
    @21
    resubcld
    @0
    @24
    cc
    wcel
    @25
    cr
    wcel
    @0
    @24
    @12
    @0
    @24
    cr
    wcel
    @15
    @3
    cA
    resubcl
    mpancom
    recnd
    @24
    abscl
    syl
    #
    @22
    @0
    @10
    @18
    @23
    @25
    cle
    wbr
    @16
    @20
    @3
    cA
    abs2dif
    syl2anc
    @0
    @25
    @1
    c1
    @26
    @13
    @0
    halfre
    a1i
    @22
    cA
    rddif
    @1
    c1
    cle
    wbr
    @0
    @1
    c1
    halfre
    1re
    halflt1
    ltleii
    a1i
    letrd
    letrd
    subled
    @0
    @19
    @5
    cz
    wcel
    #
    @9
    @8
    wb
    @21
    @0
    @4
    cz
    wcel
    @27
    @0
    @4
    @0
    @3
    cz
    wcel
    @4
    cn0
    wcel
    @0
    @2
    @14
    flcld
    @3
    nn0abscl
    syl
    nn0zd
    @4
    peano2zm
    syl
    @6
    @5
    flge
    syl2anc
    mpbid
    @0
    @4
    c1
    @7
    @17
    @22
    @0
    @19
    @7
    cr
    wcel
    @21
    @6
    reflcl
    syl
    lesubaddd
    mpbid
end
