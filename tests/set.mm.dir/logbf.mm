include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "clogb.mm"
include "ccur.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "clog.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "wa.mm"
include "eldifsn.mm"
include "logcl.mm"
include "sylbi.mm"
include "adantl.mm"
include "3adant3.mm"
include "adantr.mm"
include "logccne0.mm"
include "divcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "logbmpt.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem logbf
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. CC /\ B =/= 0 /\ B =/= 1 ) -> ( curry logb ` B ) : ( CC \ { 0 } ) --> CC )

  proof
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    #
    cc
    cc0
    csn
    cdif
    #
    cc
    cB
    clogb
    ccur
    cfv
    #
    wf
    @4
    cc
    vy
    @4
    vy
    cv
    #
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    wf
    @3
    vy
    @4
    @9
    cc
    @10
    @3
    @6
    @4
    wcel
    #
    wa
    @7
    @8
    @11
    @7
    cc
    wcel
    #
    @3
    @11
    @6
    cc
    wcel
    @6
    cc0
    wne
    wa
    @12
    @6
    cc
    cc0
    eldifsn
    @6
    logcl
    sylbi
    adantl
    @3
    @8
    cc
    wcel
    #
    @11
    @0
    @1
    @13
    @2
    cB
    logcl
    3adant3
    adantr
    @3
    @8
    cc0
    wne
    @11
    cB
    logccne0
    adantr
    divcld
    @10
    eqid
    fmptd
    @3
    @4
    cc
    @5
    @10
    vy
    cB
    logbmpt
    feq1d
    mpbird
end
