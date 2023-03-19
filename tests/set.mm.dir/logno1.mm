include "crp.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wa.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "ex.mm"
include "ssrdv.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "o1res2.mm"
include "cxr.mm"
include "wne.mm"
include "csup.mm"
include "wceq.mm"
include "rexrd.mm"
include "renepnfd.mm"
include "ioopnfsup.mm"
include "syl2anc.mm"
include "cdiv.mm"
include "cc0.mm"
include "crli.mm"
include "divlogrlim.mm"
include "rplogcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "rlimno1.mm"
include "pm2.65i.mm"

theorem logno1
  let vx: setvar x
  let vc: setvar c
  let vy: setvar y


  assert |- -. ( x e. RR+ |-> ( log ` x ) ) e. O(1)

  proof
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    #
    cmpt
    #
    co1
    wcel
    #
    vy
    c1
    cpnf
    cioo
    co
    #
    vy
    cv
    #
    clog
    cfv
    #
    cmpt
    co1
    wcel
    @3
    vy
    @4
    crp
    @6
    @3
    vy
    @4
    crp
    @3
    @5
    @4
    wcel
    #
    @5
    crp
    wcel
    @3
    @7
    wa
    #
    @5
    c1
    @7
    @5
    cr
    wcel
    @3
    @5
    c1
    cpnf
    elioore
    adantl
    #
    c1
    crp
    wcel
    @8
    1rp
    a1i
    @8
    c1
    @5
    @8
    1red
    @9
    @8
    c1
    @5
    clt
    wbr
    #
    @5
    cpnf
    clt
    wbr
    #
    @7
    @10
    @11
    wa
    @3
    @5
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    ltled
    rpgecld
    ex
    ssrdv
    @3
    vy
    crp
    @6
    cmpt
    #
    co1
    wcel
    @2
    @13
    co1
    vx
    vy
    crp
    @1
    @6
    @0
    @5
    clog
    fveq2
    cbvmptv
    eleq1i
    biimpi
    o1res2
    @3
    vy
    @4
    @6
    @3
    c1
    cxr
    wcel
    c1
    cpnf
    wne
    @4
    cxr
    clt
    csup
    cpnf
    wceq
    @3
    c1
    @3
    1red
    #
    rexrd
    @3
    c1
    @14
    renepnfd
    c1
    ioopnfsup
    syl2anc
    vy
    @4
    c1
    @6
    cdiv
    co
    cmpt
    cc0
    crli
    wbr
    @3
    vy
    divlogrlim
    a1i
    @8
    @6
    @8
    @5
    @9
    @12
    rplogcld
    #
    rpcnd
    @8
    @6
    @15
    rpne0d
    rlimno1
    pm2.65i
end
