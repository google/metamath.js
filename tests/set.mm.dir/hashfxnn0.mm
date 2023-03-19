include "cvv.mm"
include "cxnn0.mm"
include "chash.mm"
include "wf.mm"
include "cfn.mm"
include "cdif.mm"
include "cun.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
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
include "wb.mm"
include "df-hash.mm"
include "df-xnn0.mm"
include "feq123.mm"
include "mp3an.mm"
include "unvdif.mm"
include "feq2i.mm"
include "bitr4i.mm"
include "mpbir.mm"

theorem hashfxnn0
  let vx: setvar x


  assert |- # : _V --> NN0*

  proof
    cvv
    cxnn0
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
    cn0
    cpnf
    csn
    #
    cun
    #
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
    @1
    @3
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
    @1
    @3
    @7
    wf
    #
    wa
    cfn
    @1
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
    @1
    cpnf
    pnfex
    fconst
    pm3.2i
    cfn
    cvv
    disjdif
    cfn
    @1
    cn0
    @3
    @6
    @7
    fun
    mp2an
    @0
    cvv
    @4
    @8
    wf
    #
    @9
    chash
    @8
    wceq
    cvv
    cvv
    wceq
    cxnn0
    @4
    wceq
    @0
    @12
    wb
    vx
    df-hash
    cvv
    eqid
    df-xnn0
    cvv
    cxnn0
    cvv
    @4
    chash
    @8
    feq123
    mp3an
    @2
    cvv
    @4
    @8
    cfn
    unvdif
    feq2i
    bitr4i
    mpbir
end
