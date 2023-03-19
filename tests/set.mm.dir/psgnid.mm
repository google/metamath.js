include "cfn.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "csymg.mm"
include "c0g.mm"
include "c1.mm"
include "eqid.mm"
include "symgid.mm"
include "fveq2d.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "co.mm"
include "cghm.mm"
include "wceq.mm"
include "psgnghm2.mm"
include "cmnd.mm"
include "cc.mm"
include "wss.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "ax-mp.mm"
include "1ex.mm"
include "prid1.mm"
include "ax-1cn.mm"
include "negcli.mm"
include "prssi.mm"
include "mp2an.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "ress0g.mm"
include "mp3an.mm"
include "ghmid.mm"
include "syl.mm"
include "eqtrd.mm"

theorem psgnid
  let cD: class D
  let cS: class S
  assume psgnid.s: |- S = ( pmSgn ` D )


  assert |- ( D e. Fin -> ( S ` ( _I |` D ) ) = 1 )

  proof
    cD
    cfn
    wcel
    #
    cid
    cD
    cres
    #
    cS
    cfv
    cD
    csymg
    cfv
    #
    c0g
    cfv
    #
    cS
    cfv
    #
    c1
    @0
    @1
    @3
    cS
    cD
    @2
    cfn
    @2
    eqid
    #
    symgid
    fveq2d
    @0
    cS
    @2
    ccnfld
    cmgp
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    #
    cress
    co
    #
    cghm
    co
    wcel
    @4
    c1
    wceq
    cD
    @2
    @9
    cS
    @5
    psgnid.s
    @9
    eqid
    #
    psgnghm2
    @2
    @9
    cS
    @3
    c1
    @3
    eqid
    @6
    cmnd
    wcel
    #
    c1
    @8
    wcel
    @8
    cc
    wss
    #
    c1
    @9
    c0g
    cfv
    wceq
    ccnfld
    crg
    wcel
    @11
    cnring
    ccnfld
    @6
    @6
    eqid
    #
    ringmgp
    ax-mp
    c1
    @7
    1ex
    prid1
    c1
    cc
    wcel
    @7
    cc
    wcel
    @12
    ax-1cn
    c1
    ax-1cn
    negcli
    c1
    @7
    cc
    prssi
    mp2an
    @8
    cc
    @6
    @9
    c1
    @10
    cc
    ccnfld
    @6
    @13
    cnfldbas
    mgpbas
    ccnfld
    c1
    @6
    @13
    cnfld1
    ringidval
    ress0g
    mp3an
    ghmid
    syl
    eqtrd
end
