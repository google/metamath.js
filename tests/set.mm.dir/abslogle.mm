include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cabs.mm"
include "cim.mm"
include "caddc.mm"
include "co.mm"
include "cpi.mm"
include "logcl.mm"
include "abscld.mm"
include "crp.mm"
include "cr.mm"
include "absrpcl.mm"
include "relogcl.mm"
include "syl.mm"
include "recnd.mm"
include "imcld.mm"
include "readdcld.mm"
include "pire.mm"
include "a1i.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "cle.mm"
include "recld.mm"
include "ax-icn.mm"
include "mulcld.mm"
include "abstrid.mm"
include "replimd.mm"
include "fveq2d.mm"
include "relog.mm"
include "eqcomd.mm"
include "absmuld.mm"
include "c1.mm"
include "absi.mm"
include "oveq1i.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "abslogimle.mm"
include "leadd2dd.mm"
include "letrd.mm"

theorem abslogle
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( abs ` ( log ` A ) ) <_ ( ( abs ` ( log ` ( abs ` A ) ) ) + _pi ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    #
    cA
    clog
    cfv
    #
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    clog
    cfv
    #
    cabs
    cfv
    #
    @1
    cim
    cfv
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @5
    cpi
    caddc
    co
    @0
    @1
    cA
    logcl
    #
    abscld
    @0
    @5
    @7
    @0
    @4
    @0
    @4
    @0
    @3
    crp
    wcel
    @4
    cr
    wcel
    cA
    absrpcl
    @3
    relogcl
    syl
    recnd
    abscld
    #
    @0
    @6
    @0
    @6
    @0
    @1
    @9
    imcld
    recnd
    #
    abscld
    #
    readdcld
    @0
    @5
    cpi
    @10
    cpi
    cr
    wcel
    @0
    pire
    a1i
    #
    readdcld
    @0
    @1
    cre
    cfv
    #
    ci
    @6
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    @14
    cabs
    cfv
    #
    @15
    cabs
    cfv
    #
    caddc
    co
    @2
    @8
    cle
    @0
    @14
    @15
    @0
    @14
    @0
    @1
    @9
    recld
    recnd
    @0
    ci
    @6
    ci
    cc
    wcel
    @0
    ax-icn
    a1i
    #
    @11
    mulcld
    abstrid
    @0
    @1
    @16
    cabs
    @0
    @1
    @9
    replimd
    fveq2d
    @0
    @5
    @17
    @7
    @18
    caddc
    @0
    @4
    @14
    cabs
    @0
    @14
    @4
    cA
    relog
    eqcomd
    fveq2d
    @0
    @18
    ci
    cabs
    cfv
    #
    @7
    cmul
    co
    #
    @7
    @0
    ci
    @6
    @19
    @11
    absmuld
    @0
    @21
    c1
    @7
    cmul
    co
    @7
    @20
    c1
    @7
    cmul
    absi
    oveq1i
    @0
    @7
    @0
    @7
    @12
    recnd
    mulid2d
    syl5eq
    eqtr2d
    oveq12d
    3brtr4d
    @0
    @7
    cpi
    @5
    @12
    @13
    @10
    cA
    abslogimle
    leadd2dd
    letrd
end
