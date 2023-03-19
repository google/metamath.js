include "clog.mm"
include "crp.mm"
include "cres.mm"
include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wf1o.mm"
include "relogf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "rpssre.mm"
include "w3a.mm"
include "cdv.mm"
include "cdm.mm"
include "wceq.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "ovex.mm"
include "dvrelog.mm"
include "dmmpti.mm"
include "dvcn.mm"
include "mpan2.mm"
include "mp3an.mm"
include "cncffvrn.mm"
include "mpbir.mm"

theorem relogcn
  let vx: setvar x


  assert |- ( log |` RR+ ) e. ( RR+ -cn-> RR )

  proof
    clog
    crp
    cres
    #
    crp
    cr
    ccncf
    co
    wcel
    #
    crp
    cr
    @0
    wf
    #
    crp
    cr
    @0
    wf1o
    @2
    relogf1o
    crp
    cr
    @0
    f1of
    ax-mp
    #
    cr
    cc
    wss
    #
    @0
    crp
    cc
    ccncf
    co
    wcel
    #
    @1
    @2
    wb
    ax-resscn
    @4
    crp
    cc
    @0
    wf
    #
    crp
    cr
    wss
    #
    @5
    ax-resscn
    @2
    @4
    @6
    @3
    ax-resscn
    crp
    cr
    cc
    @0
    fss
    mp2an
    rpssre
    @4
    @6
    @7
    w3a
    cr
    @0
    cdv
    co
    #
    cdm
    crp
    wceq
    @5
    vx
    crp
    c1
    vx
    cv
    #
    cdiv
    co
    @8
    c1
    @9
    cdiv
    ovex
    vx
    dvrelog
    dmmpti
    crp
    cr
    @0
    dvcn
    mpan2
    mp3an
    crp
    cc
    cr
    @0
    cncffvrn
    mp2an
    mpbir
end
