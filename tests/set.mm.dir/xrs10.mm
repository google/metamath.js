include "cc0.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cxad.mm"
include "wss.mm"
include "cbs.mm"
include "difss.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "xrex.mm"
include "ssexi.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "cr.mm"
include "0re.mm"
include "wne.mm"
include "rexr.mm"
include "renemnf.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "mp1i.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "eldifi.mm"
include "adantl.mm"
include "xaddid2.mm"
include "syl.mm"
include "xaddid1.mm"
include "ismgmid2.mm"
include "trud.mm"

theorem xrs10
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrs1mnd.1: |- R = ( RR*s |`s ( RR* \ { -oo } ) )


  assert |- 0 = ( 0g ` R )

  proof
    cc0
    cR
    c0g
    cfv
    #
    wceq
    wtru
    vx
    cxr
    cmnf
    csn
    #
    cdif
    #
    cxad
    cc0
    cR
    @0
    @2
    cxr
    wss
    @2
    cR
    cbs
    cfv
    wceq
    cxr
    @1
    difss
    #
    @2
    cxr
    cR
    cxrs
    xrs1mnd.1
    xrsbas
    ressbas2
    ax-mp
    @0
    eqid
    @2
    cvv
    wcel
    cxad
    cR
    cplusg
    cfv
    wceq
    @2
    cxr
    xrex
    @3
    ssexi
    @2
    cxad
    cxrs
    cR
    cvv
    xrs1mnd.1
    xrsadd
    ressplusg
    ax-mp
    cc0
    cr
    wcel
    #
    cc0
    @2
    wcel
    #
    wtru
    0re
    @4
    cc0
    cxr
    wcel
    cc0
    cmnf
    wne
    @5
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
    vx
    cv
    #
    @2
    wcel
    #
    wa
    #
    @6
    cxr
    wcel
    #
    cc0
    @6
    cxad
    co
    @6
    wceq
    @7
    @9
    wtru
    @6
    cxr
    @1
    eldifi
    adantl
    #
    @6
    xaddid2
    syl
    @8
    @9
    @6
    cc0
    cxad
    co
    @6
    wceq
    @10
    @6
    xaddid1
    syl
    ismgmid2
    trud
end
