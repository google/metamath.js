include "cvv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "chash.mm"
include "wf.mm"
include "cfn.mm"
include "cdif.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "ccrd.mm"
include "ccom.mm"
include "cxp.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "eqid.mm"
include "hashkf.mm"
include "pnfex.mm"
include "fconst.mm"
include "pm3.2i.mm"
include "disjdif.mm"
include "fun.mm"
include "mp2an.mm"
include "df-hash.mm"
include "feq1i.mm"
include "unvdif.mm"
include "feq2i.mm"
include "bitr4i.mm"
include "mpbir.mm"

theorem hashfOLD
  let vx: setvar x


  assert |- # : _V --> ( NN0 u. { +oo } )

  proof
    cvv
    cn0
    cpnf
    csn
    #
    cun
    #
    chash
    wf
    #
    cfn
    cvv
    cfn
    cdif
    #
    cun
    #
    @1
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    ccrd
    ccom
    #
    @3
    @0
    cxp
    #
    cun
    #
    wf
    #
    cfn
    cn0
    @6
    wf
    #
    @3
    @0
    @7
    wf
    #
    wa
    cfn
    @3
    cin
    c0
    wceq
    @9
    @10
    @11
    vx
    @5
    @6
    @5
    eqid
    @6
    eqid
    hashkf
    @3
    cpnf
    pnfex
    fconst
    pm3.2i
    cfn
    cvv
    disjdif
    cfn
    @3
    cn0
    @0
    @6
    @7
    fun
    mp2an
    @2
    cvv
    @1
    @8
    wf
    @9
    cvv
    @1
    chash
    @8
    vx
    df-hash
    feq1i
    @4
    cvv
    @1
    @8
    cfn
    unvdif
    feq2i
    bitr4i
    mpbir
end
