include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "ceu.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "clogb.mm"
include "ccur.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "loge.mm"
include "a1i.mm"
include "oveq2d.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "logcl.mm"
include "sylbi.mm"
include "div1d.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "ere.mm"
include "recni.mm"
include "crp.mm"
include "epr.mm"
include "rpne0.mm"
include "ax-mp.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c3.mm"
include "egt2lt3.mm"
include "wo.mm"
include "cr.mm"
include "w3a.mm"
include "wi.mm"
include "1re.mm"
include "2re.mm"
include "3pm3.2i.mm"
include "1lt2.mm"
include "lttr.mm"
include "expd.mm"
include "mp2.mm"
include "olcd.mm"
include "wb.mm"
include "pm3.2i.mm"
include "lttri2.mm"
include "mp1i.mm"
include "mpbird.mm"
include "adantr.mm"
include "logbmpt.mm"
include "mp3an.mm"
include "wfn.mm"
include "crn.mm"
include "wf1o.mm"
include "logf1o.mm"
include "f1ofn.mm"
include "dffn5.mm"
include "mpbi.mm"
include "3eqtr4i.mm"

theorem logblog
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( curry logb ` _e ) = log

  proof
    vy
    cc
    cc0
    csn
    cdif
    #
    vy
    cv
    #
    clog
    cfv
    #
    ceu
    clog
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    vy
    @0
    @2
    cmpt
    #
    ceu
    clogb
    ccur
    cfv
    #
    clog
    vy
    @0
    @4
    @2
    @1
    @0
    wcel
    #
    @4
    @2
    c1
    cdiv
    co
    @2
    @8
    @3
    c1
    @2
    cdiv
    @3
    c1
    wceq
    @8
    loge
    a1i
    oveq2d
    @8
    @2
    @8
    @1
    cc
    wcel
    @1
    cc0
    wne
    wa
    @2
    cc
    wcel
    @1
    cc
    cc0
    eldifsn
    @1
    logcl
    sylbi
    div1d
    eqtrd
    mpteq2ia
    ceu
    cc
    wcel
    ceu
    cc0
    wne
    #
    ceu
    c1
    wne
    #
    @7
    @5
    wceq
    ceu
    ere
    recni
    ceu
    crp
    wcel
    @9
    epr
    ceu
    rpne0
    ax-mp
    c2
    ceu
    clt
    wbr
    #
    ceu
    c3
    clt
    wbr
    #
    wa
    @10
    egt2lt3
    @11
    @10
    @12
    @11
    @10
    ceu
    c1
    clt
    wbr
    #
    c1
    ceu
    clt
    wbr
    #
    wo
    #
    @11
    @14
    @13
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    ceu
    cr
    wcel
    #
    w3a
    #
    c1
    c2
    clt
    wbr
    #
    @11
    @14
    wi
    @16
    @17
    @18
    1re
    2re
    ere
    3pm3.2i
    1lt2
    @19
    @20
    @11
    @14
    c1
    c2
    ceu
    lttr
    expd
    mp2
    olcd
    @18
    @16
    wa
    @10
    @15
    wb
    @11
    @18
    @16
    ere
    1re
    pm3.2i
    ceu
    c1
    lttri2
    mp1i
    mpbird
    adantr
    ax-mp
    vy
    ceu
    logbmpt
    mp3an
    clog
    @0
    wfn
    #
    clog
    @6
    wceq
    @0
    clog
    crn
    #
    clog
    wf1o
    @21
    logf1o
    @0
    @22
    clog
    f1ofn
    ax-mp
    vy
    @0
    clog
    dffn5
    mpbi
    3eqtr4i
end
