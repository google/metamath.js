include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "cle.mm"
include "rpcn.mm"
include "1cnd.mm"
include "rpne0.mm"
include "divdird.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "mpan2.mm"
include "relogdiv.mm"
include "mpancom.mm"
include "eqtrd.mm"
include "wbr.mm"
include "ce.mm"
include "rpreccl.mm"
include "sylancr.mm"
include "reeflogd.mm"
include "rpred.mm"
include "reefcld.mm"
include "clt.mm"
include "efgt1p.mm"
include "syl.mm"
include "ltled.mm"
include "eqbrtrd.mm"
include "cr.mm"
include "wb.mm"
include "relogcl.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "efle.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"

theorem logdifbnd
  let cA: class A


  assert |- ( A e. RR+ -> ( ( log ` ( A + 1 ) ) - ( log ` A ) ) <_ ( 1 / A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    c1
    cA
    cdiv
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    cA
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    cmin
    co
    #
    @1
    cle
    @0
    @3
    @4
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    @7
    @0
    @2
    @8
    clog
    @0
    @8
    cA
    cA
    cdiv
    co
    #
    @1
    caddc
    co
    @2
    @0
    cA
    c1
    cA
    cA
    rpcn
    #
    @0
    1cnd
    @11
    cA
    rpne0
    #
    divdird
    @0
    @10
    c1
    @1
    caddc
    @0
    cA
    @11
    @12
    dividd
    oveq1d
    eqtr2d
    fveq2d
    @4
    crp
    wcel
    #
    @0
    @9
    @7
    wceq
    @0
    c1
    crp
    wcel
    #
    @13
    1rp
    cA
    c1
    rpaddcl
    mpan2
    #
    @4
    cA
    relogdiv
    mpancom
    eqtrd
    #
    @0
    @3
    @1
    cle
    wbr
    #
    @3
    ce
    cfv
    #
    @1
    ce
    cfv
    #
    cle
    wbr
    #
    @0
    @18
    @2
    @19
    cle
    @0
    @2
    @0
    @14
    @1
    crp
    wcel
    #
    @2
    crp
    wcel
    1rp
    cA
    rpreccl
    #
    c1
    @1
    rpaddcl
    sylancr
    #
    reeflogd
    @0
    @2
    @19
    @0
    @2
    @23
    rpred
    @0
    @1
    @0
    @1
    @22
    rpred
    #
    reefcld
    @0
    @21
    @2
    @19
    clt
    wbr
    @22
    @1
    efgt1p
    syl
    ltled
    eqbrtrd
    @0
    @3
    cr
    wcel
    @1
    cr
    wcel
    @17
    @20
    wb
    @0
    @3
    @7
    cr
    @16
    @0
    @5
    @6
    @0
    @13
    @5
    cr
    wcel
    @15
    @4
    relogcl
    syl
    cA
    relogcl
    resubcld
    eqeltrd
    @24
    @3
    @1
    efle
    syl2anc
    mpbird
    eqbrtrrd
end
