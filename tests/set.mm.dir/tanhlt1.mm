include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "cdiv.mm"
include "ce.mm"
include "cneg.mm"
include "cmin.mm"
include "caddc.mm"
include "c1.mm"
include "clt.mm"
include "c2.mm"
include "csin.mm"
include "ccos.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "rpcoshcl.mm"
include "rpne0d.mm"
include "tanval.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "sincld.mm"
include "recoshcl.mm"
include "recnd.mm"
include "a1i.mm"
include "ine0.mm"
include "divdiv32d.mm"
include "sinhval.mm"
include "syl.mm"
include "coshval.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "reefcl.mm"
include "renegcl.mm"
include "reefcld.mm"
include "resubcld.mm"
include "readdcld.mm"
include "2cnd.mm"
include "eqnetrrd.mm"
include "2ne0.mm"
include "divne0bd.mm"
include "mpbird.mm"
include "divcan7d.mm"
include "eqtrd.mm"
include "wbr.mm"
include "rpefcld.mm"
include "ltsubrpd.mm"
include "ltaddrpd.mm"
include "lttrd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "1red.mm"
include "efgt0.mm"
include "addgt0d.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "eqbrtrd.mm"

theorem tanhlt1
  let cA: class A


  assert |- ( A e. RR -> ( ( tan ` ( _i x. A ) ) / _i ) < 1 )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    #
    cA
    ce
    cfv
    #
    cA
    cneg
    #
    ce
    cfv
    #
    cmin
    co
    #
    @4
    @6
    caddc
    co
    #
    cdiv
    co
    #
    c1
    clt
    @0
    @3
    @7
    c2
    cdiv
    co
    #
    @8
    c2
    cdiv
    co
    #
    cdiv
    co
    #
    @9
    @0
    @3
    @1
    csin
    cfv
    #
    @1
    ccos
    cfv
    #
    cdiv
    co
    #
    ci
    cdiv
    co
    @13
    ci
    cdiv
    co
    #
    @14
    cdiv
    co
    @12
    @0
    @2
    @15
    ci
    cdiv
    @0
    @1
    cc
    wcel
    #
    @14
    cc0
    wne
    @2
    @15
    wceq
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @17
    ax-icn
    cA
    recn
    #
    ci
    cA
    mulcl
    sylancr
    #
    @0
    @14
    cA
    rpcoshcl
    rpne0d
    #
    @1
    tanval
    syl2anc
    oveq1d
    @0
    @13
    @14
    ci
    @0
    @1
    @21
    sincld
    @0
    @14
    cA
    recoshcl
    recnd
    @18
    @0
    ax-icn
    a1i
    @22
    ci
    cc0
    wne
    @0
    ine0
    a1i
    divdiv32d
    @0
    @16
    @10
    @14
    @11
    cdiv
    @0
    @19
    @16
    @10
    wceq
    @20
    cA
    sinhval
    syl
    @0
    @19
    @14
    @11
    wceq
    @20
    cA
    coshval
    syl
    #
    oveq12d
    3eqtrd
    @0
    @7
    @8
    c2
    @0
    @7
    @0
    @4
    @6
    cA
    reefcl
    #
    @0
    @5
    cA
    renegcl
    #
    reefcld
    #
    resubcld
    #
    recnd
    @0
    @8
    @0
    @4
    @6
    @24
    @26
    readdcld
    #
    recnd
    #
    @0
    2cnd
    #
    @0
    @8
    cc0
    wne
    @11
    cc0
    wne
    @0
    @14
    @11
    cc0
    @23
    @22
    eqnetrrd
    @0
    @8
    c2
    @29
    @30
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    divne0bd
    mpbird
    @31
    divcan7d
    eqtrd
    @0
    @9
    c1
    clt
    wbr
    #
    @7
    @8
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @0
    @7
    @8
    @33
    clt
    @0
    @7
    @4
    @8
    @27
    @24
    @28
    @0
    @4
    @6
    @24
    @0
    @5
    @25
    rpefcld
    #
    ltsubrpd
    @0
    @4
    @6
    @24
    @35
    ltaddrpd
    lttrd
    @0
    @8
    @29
    mulid1d
    breqtrrd
    @0
    @7
    cr
    wcel
    c1
    cr
    wcel
    @8
    cr
    wcel
    cc0
    @8
    clt
    wbr
    @32
    @34
    wb
    @27
    @0
    1red
    @28
    @0
    @4
    @6
    @24
    @26
    cA
    efgt0
    @0
    @5
    cr
    wcel
    cc0
    @6
    clt
    wbr
    @25
    @5
    efgt0
    syl
    addgt0d
    @7
    c1
    @8
    ltdivmul
    syl112anc
    mpbird
    eqbrtrd
end
