include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "wtru.mm"
include "wf.mm"
include "0re.mm"
include "fconst6.mm"
include "a1i.mm"
include "crn.mm"
include "cfn.mm"
include "wss.mm"
include "snfi.mm"
include "rnxpss.mm"
include "ssfi.mm"
include "mp2an.mm"
include "cv.mm"
include "cdif.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "difss.mm"
include "sstri.mm"
include "sseli.mm"
include "adantl.mm"
include "wn.mm"
include "eldifn.mm"
include "pm2.21dd.mm"
include "cfv.mm"
include "i1fd.mm"
include "trud.mm"

theorem i1f0
  let vx: setvar x


  assert |- ( RR X. { 0 } ) e. dom S.1

  proof
    cr
    cc0
    csn
    #
    cxp
    #
    citg1
    cdm
    wcel
    wtru
    vx
    @1
    cr
    cr
    @1
    wf
    wtru
    cr
    cc0
    cr
    0re
    fconst6
    a1i
    @1
    crn
    #
    cfn
    wcel
    #
    wtru
    @0
    cfn
    wcel
    @2
    @0
    wss
    @3
    cc0
    snfi
    cr
    @0
    rnxpss
    #
    @0
    @2
    ssfi
    mp2an
    a1i
    wtru
    vx
    cv
    #
    @2
    @0
    cdif
    #
    wcel
    #
    wa
    #
    @5
    @0
    wcel
    #
    @1
    ccnv
    @5
    csn
    cima
    #
    cvol
    cdm
    wcel
    @7
    @9
    wtru
    @6
    @0
    @5
    @6
    @2
    @0
    @2
    @0
    difss
    @4
    sstri
    sseli
    adantl
    #
    @7
    @9
    wn
    wtru
    @5
    @2
    @0
    eldifn
    adantl
    #
    pm2.21dd
    @8
    @9
    @10
    cvol
    cfv
    cr
    wcel
    @11
    @12
    pm2.21dd
    i1fd
    trud
end
