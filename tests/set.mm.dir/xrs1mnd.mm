include "cmnd.mm"
include "wcel.mm"
include "wtru.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cxad.mm"
include "cc0.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "difss.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "mp1i.mm"
include "cvv.mm"
include "cplusg.mm"
include "xrex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "xaddcl.mm"
include "ad2ant2r.mm"
include "xaddnemnf.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "3adant1.mm"
include "w3a.mm"
include "xaddass.mm"
include "syl3anb.mm"
include "adantl.mm"
include "cr.mm"
include "0re.mm"
include "rexr.mm"
include "renemnf.mm"
include "eldifi.mm"
include "xaddid2.mm"
include "syl.mm"
include "xaddid1.mm"
include "ismndd.mm"
include "trud.mm"

theorem xrs1mnd
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrs1mnd.1: |- R = ( RR*s |`s ( RR* \ { -oo } ) )


  assert |- R e. Mnd

  proof
    cR
    cmnd
    wcel
    wtru
    vx
    vy
    vz
    cxr
    cmnf
    csn
    #
    cdif
    #
    cxad
    cR
    cc0
    @1
    cxr
    wss
    @1
    cR
    cbs
    cfv
    wceq
    wtru
    cxr
    @0
    difss
    @1
    cxr
    cR
    cxrs
    xrs1mnd.1
    xrsbas
    ressbas2
    mp1i
    @1
    cvv
    wcel
    #
    cxad
    cR
    cplusg
    cfv
    wceq
    wtru
    cxr
    cvv
    wcel
    @2
    xrex
    cxr
    @0
    cvv
    difexg
    ax-mp
    @1
    cxad
    cxrs
    cR
    cvv
    xrs1mnd.1
    xrsadd
    ressplusg
    mp1i
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    @3
    @5
    cxad
    co
    #
    @1
    wcel
    #
    wtru
    @4
    @3
    cxr
    wcel
    #
    @3
    cmnf
    wne
    #
    wa
    #
    @5
    cxr
    wcel
    #
    @5
    cmnf
    wne
    #
    wa
    #
    @8
    @6
    @3
    cxr
    cmnf
    eldifsn
    #
    @5
    cxr
    cmnf
    eldifsn
    #
    @11
    @14
    wa
    @7
    cxr
    wcel
    #
    @7
    cmnf
    wne
    @8
    @9
    @12
    @17
    @10
    @13
    @3
    @5
    xaddcl
    ad2ant2r
    @3
    @5
    xaddnemnf
    @7
    cxr
    cmnf
    eldifsn
    sylanbrc
    syl2anb
    3adant1
    @4
    @6
    vz
    cv
    #
    @1
    wcel
    #
    w3a
    @7
    @18
    cxad
    co
    @3
    @5
    @18
    cxad
    co
    cxad
    co
    wceq
    #
    wtru
    @4
    @11
    @6
    @14
    @19
    @18
    cxr
    wcel
    @18
    cmnf
    wne
    wa
    @20
    @15
    @16
    @18
    cxr
    cmnf
    eldifsn
    @3
    @5
    @18
    xaddass
    syl3anb
    adantl
    cc0
    cr
    wcel
    #
    cc0
    @1
    wcel
    #
    wtru
    0re
    @21
    cc0
    cxr
    wcel
    cc0
    cmnf
    wne
    @22
    cc0
    rexr
    cc0
    renemnf
    cc0
    cxr
    cmnf
    eldifsn
    sylanbrc
    mp1i
    wtru
    @4
    wa
    #
    @9
    cc0
    @3
    cxad
    co
    @3
    wceq
    @4
    @9
    wtru
    @3
    cxr
    @0
    eldifi
    adantl
    #
    @3
    xaddid2
    syl
    @23
    @9
    @3
    cc0
    cxad
    co
    @3
    wceq
    @24
    @3
    xaddid1
    syl
    ismndd
    trud
end
