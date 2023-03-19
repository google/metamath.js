include "c0.mm"
include "csn.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "f0.mm"
include "cnv0.mm"
include "imaeq1i.mm"
include "0ima.mm"
include "eqtri.mm"
include "0ex.mm"
include "snid.mm"
include "eqeltri.mm"
include "rgenw.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "wb.mm"
include "sn0topon.mm"
include "iscn.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem 0cnf
  let vk: setvar k
  let vx: setvar x


  assert |- (/) e. ( { (/) } Cn { (/) } )

  proof
    c0
    c0
    csn
    #
    @0
    ccn
    co
    wcel
    #
    c0
    c0
    c0
    wf
    #
    c0
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @0
    wcel
    #
    vx
    @0
    wral
    #
    c0
    f0
    @6
    vx
    @0
    @5
    c0
    @0
    @5
    c0
    @4
    cima
    c0
    @3
    c0
    @4
    cnv0
    imaeq1i
    @4
    0ima
    eqtri
    c0
    0ex
    snid
    eqeltri
    rgenw
    @0
    c0
    ctopon
    cfv
    wcel
    #
    @8
    @1
    @2
    @7
    wa
    wb
    sn0topon
    sn0topon
    vx
    c0
    @0
    @0
    c0
    c0
    iscn
    mp2an
    mpbir2an
end
