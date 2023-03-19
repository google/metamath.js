include "cii.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "chmph.mm"
include "wbr.mm"
include "cle.mm"
include "cordt.mm"
include "cc0.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "chmeo.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "neg1rr.mm"
include "1re.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "eqid.mm"
include "icchmeo.mm"
include "mp3an.mm"
include "hmphi.mm"
include "ax-mp.mm"
include "wceq.mm"
include "cpnf.mm"
include "cdiv.mm"
include "cif.mm"
include "cxne.mm"
include "cxr.mm"
include "wiso.mm"
include "xrhmeo.mm"
include "simpri.mm"
include "hmphtr.mm"

theorem xrhmph
  let vx: setvar x
  let vy: setvar y


  assert |- II ~= ( ordTop ` <_ )

  proof
    cii
    ccnfld
    ctopn
    cfv
    #
    c1
    cneg
    #
    c1
    cicc
    co
    #
    crest
    co
    #
    chmph
    wbr
    #
    @3
    cle
    cordt
    cfv
    #
    chmph
    wbr
    #
    cii
    @5
    chmph
    wbr
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    cmul
    co
    c1
    @8
    cmin
    co
    #
    @1
    cmul
    co
    caddc
    co
    cmpt
    #
    cii
    @3
    chmeo
    co
    wcel
    #
    @4
    @1
    cr
    wcel
    c1
    cr
    wcel
    @1
    c1
    clt
    wbr
    #
    @11
    neg1rr
    1re
    @1
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @12
    neg1lt0
    0lt1
    @1
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    vx
    @1
    c1
    @10
    @0
    @0
    eqid
    #
    @10
    eqid
    icchmeo
    mp3an
    @10
    cii
    @3
    hmphi
    ax-mp
    vy
    @2
    cc0
    vy
    cv
    #
    cle
    wbr
    @14
    vx
    @7
    @8
    c1
    wceq
    cpnf
    @8
    @9
    cdiv
    co
    cif
    cmpt
    #
    cfv
    @14
    cneg
    @15
    cfv
    cxne
    cif
    cmpt
    #
    @3
    @5
    chmeo
    co
    wcel
    #
    @6
    @2
    cxr
    clt
    clt
    @16
    wiso
    @17
    vx
    vy
    @15
    @16
    @0
    @5
    @15
    eqid
    @16
    eqid
    @13
    @5
    eqid
    xrhmeo
    simpri
    @16
    @3
    @5
    hmphi
    ax-mp
    cii
    @3
    @5
    hmphtr
    mp2an
end
