include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cre.mm"
include "cmin.mm"
include "co.mm"
include "ce.mm"
include "cdiv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "cabs.mm"
include "wceq.mm"
include "logcl.mm"
include "recld.mm"
include "recnd.mm"
include "efsub.mm"
include "syl2anc.mm"
include "caddc.mm"
include "replimd.mm"
include "eqcomd.mm"
include "ax-icn.mm"
include "imcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subaddd.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "eflog.mm"
include "relog.mm"
include "cr.mm"
include "abscl.mm"
include "adantr.mm"
include "absrpcl.mm"
include "rpne0d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem efiarg
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( exp ` ( _i x. ( Im ` ( log ` A ) ) ) ) = ( A / ( abs ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    clog
    cfv
    #
    @3
    cre
    cfv
    #
    cmin
    co
    #
    ce
    cfv
    #
    @3
    ce
    cfv
    #
    @4
    ce
    cfv
    #
    cdiv
    co
    #
    ci
    @3
    cim
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    cA
    cA
    cabs
    cfv
    #
    cdiv
    co
    @2
    @3
    cc
    wcel
    @4
    cc
    wcel
    @6
    @9
    wceq
    cA
    logcl
    #
    @2
    @4
    @2
    @3
    @13
    recld
    recnd
    #
    @3
    @4
    efsub
    syl2anc
    @2
    @5
    @11
    ce
    @2
    @5
    @11
    wceq
    @4
    @11
    caddc
    co
    #
    @3
    wceq
    @2
    @3
    @15
    @2
    @3
    @13
    replimd
    eqcomd
    @2
    @3
    @4
    @11
    @13
    @14
    @2
    ci
    cc
    wcel
    @10
    cc
    wcel
    @11
    cc
    wcel
    ax-icn
    @2
    @10
    @2
    @3
    @13
    imcld
    recnd
    ci
    @10
    mulcl
    sylancr
    subaddd
    mpbird
    fveq2d
    @2
    @7
    cA
    @8
    @12
    cdiv
    cA
    eflog
    @2
    @8
    @12
    clog
    cfv
    #
    ce
    cfv
    #
    @12
    @2
    @4
    @16
    ce
    cA
    relog
    fveq2d
    @2
    @12
    cc
    wcel
    @12
    cc0
    wne
    @17
    @12
    wceq
    @2
    @12
    @0
    @12
    cr
    wcel
    @1
    cA
    abscl
    adantr
    recnd
    @2
    @12
    cA
    absrpcl
    rpne0d
    @12
    eflog
    syl2anc
    eqtrd
    oveq12d
    3eqtr3d
end
