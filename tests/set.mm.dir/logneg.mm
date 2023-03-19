include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ce.mm"
include "cneg.mm"
include "c1.mm"
include "cc.mm"
include "wceq.mm"
include "relogcl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "efadd.mm"
include "sylancl.mm"
include "efipi.mm"
include "oveq2i.mm"
include "reeflog.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "rpcn.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "crn.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "addcl.mm"
include "cc0.mm"
include "pipos.mm"
include "cr.mm"
include "wb.mm"
include "pire.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "renegcli.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "crim.mm"
include "syl5breqr.mm"
include "leidi.mm"
include "syl6eqbr.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "logef.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem logneg
  let cA: class A


  assert |- ( A e. RR+ -> ( log ` -u A ) = ( ( log ` A ) + ( _i x. _pi ) ) )

  proof
    cA
    crp
    wcel
    #
    cA
    clog
    cfv
    #
    ci
    cpi
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    cA
    cneg
    #
    clog
    cfv
    @3
    @0
    @4
    @6
    clog
    @0
    @4
    @1
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    cmul
    co
    #
    cA
    c1
    cneg
    #
    cmul
    co
    #
    @6
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @4
    @9
    wceq
    @0
    @1
    cA
    relogcl
    #
    recnd
    #
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    @1
    @2
    efadd
    sylancl
    @0
    @9
    @7
    @10
    cmul
    co
    @11
    @8
    @10
    @7
    cmul
    efipi
    oveq2i
    @0
    @7
    cA
    @10
    cmul
    cA
    reeflog
    oveq1d
    syl5eq
    @0
    @11
    @10
    cA
    cmul
    co
    #
    @6
    @0
    cA
    cc
    wcel
    @10
    cc
    wcel
    @11
    @17
    wceq
    cA
    rpcn
    #
    neg1cn
    cA
    @10
    mulcom
    sylancl
    @0
    cA
    @18
    mulm1d
    eqtrd
    3eqtrd
    fveq2d
    @0
    @3
    clog
    crn
    wcel
    #
    @5
    @3
    wceq
    @0
    @3
    cc
    wcel
    #
    cpi
    cneg
    #
    @3
    cim
    cfv
    #
    clt
    wbr
    @22
    cpi
    cle
    wbr
    @19
    @0
    @12
    @13
    @20
    @15
    @16
    @1
    @2
    addcl
    sylancl
    @0
    @21
    cpi
    @22
    clt
    @21
    cc0
    clt
    wbr
    #
    cc0
    cpi
    clt
    wbr
    #
    @21
    cpi
    clt
    wbr
    @24
    @23
    pipos
    cpi
    cr
    wcel
    #
    @24
    @23
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    pipos
    @21
    cc0
    cpi
    cpi
    pire
    renegcli
    0re
    pire
    lttri
    mp2an
    @0
    @1
    cr
    wcel
    @25
    @22
    cpi
    wceq
    @14
    pire
    @1
    cpi
    crim
    sylancl
    #
    syl5breqr
    @0
    @22
    cpi
    cpi
    cle
    @26
    cpi
    pire
    leidi
    syl6eqbr
    @3
    ellogrn
    syl3anbrc
    @3
    logef
    syl
    eqtr3d
end
