include "cn.mm"
include "cr.mm"
include "wfo.mm"
include "crn.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "forn.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "cv.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cop.mm"
include "cif.mm"
include "csb.mm"
include "cmpt2.mm"
include "wex.mm"
include "wn.mm"
include "reex.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "isseti.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "csn.mm"
include "cun.mm"
include "cseq.mm"
include "ccom.mm"
include "csup.mm"
include "wcel.mm"
include "wf.mm"
include "fof.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "ruclem12.mm"
include "n0i.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpi.mm"
include "pm2.65i.mm"

theorem ruclem13
  let cF: class F
  let vd: setvar d
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y


  assert |- -. F : NN -onto-> RR

  proof
    cn
    cr
    cF
    wfo
    #
    cr
    cF
    crn
    #
    cdif
    #
    c0
    wceq
    #
    @0
    @2
    cr
    cr
    cdif
    c0
    @0
    @1
    cr
    cr
    cn
    cr
    cF
    forn
    difeq2d
    cr
    difid
    syl6eq
    @0
    vd
    cv
    #
    vx
    vy
    cr
    cr
    cxp
    #
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    caddc
    co
    c2
    cdiv
    co
    vm
    cv
    #
    vy
    cv
    clt
    wbr
    @7
    @9
    cop
    @9
    @8
    caddc
    co
    c2
    cdiv
    co
    @8
    cop
    cif
    csb
    #
    cmpt2
    #
    wceq
    #
    vd
    wex
    @3
    wn
    #
    vd
    @11
    vx
    vy
    @5
    cr
    @10
    cr
    cr
    reex
    reex
    xpex
    reex
    mpt2ex
    isseti
    @0
    @12
    @13
    vd
    @0
    @12
    @13
    @0
    @12
    wa
    #
    c1st
    @4
    cc0
    cc0
    c1
    cop
    cop
    csn
    cF
    cun
    #
    cc0
    cseq
    #
    ccom
    crn
    cr
    clt
    csup
    #
    @2
    wcel
    @13
    @14
    vx
    vy
    @15
    @4
    @17
    vm
    cF
    @16
    @0
    cn
    cr
    cF
    wf
    @12
    cn
    cr
    cF
    fof
    adantr
    @0
    @12
    simpr
    @15
    eqid
    @16
    eqid
    @17
    eqid
    ruclem12
    @2
    @17
    n0i
    syl
    ex
    exlimdv
    mpi
    pm2.65i
end
