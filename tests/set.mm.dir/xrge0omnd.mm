include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "comnd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctos.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "wi.mm"
include "wral.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "ax-mp.mm"
include "cpo.mm"
include "wo.mm"
include "ovex.mm"
include "xrge0base.mm"
include "xrge0le.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseli.mm"
include "xrleid.mm"
include "syl.mm"
include "wa.mm"
include "wceq.mm"
include "xrletri3.mm"
include "biimprd.mm"
include "syl2an.mm"
include "xrletr.mm"
include "syl3an.mm"
include "isposi.mm"
include "xrletri.mm"
include "rgen2a.mm"
include "istos.mm"
include "mpbir2an.mm"
include "w3a.mm"
include "xleadd1a.mm"
include "ex.mm"
include "rgen3.mm"
include "xrge0plusg.mm"
include "isomnd.mm"
include "mpbir3an.mm"

theorem xrge0omnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( RR*s |`s ( 0 [,] +oo ) ) e. oMnd

  proof
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    comnd
    wcel
    @1
    cmnd
    wcel
    #
    @1
    ctos
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @4
    vz
    cv
    #
    cxad
    co
    @5
    @7
    cxad
    co
    cle
    wbr
    #
    wi
    #
    vz
    @0
    wral
    vy
    @0
    wral
    vx
    @0
    wral
    @1
    ccmn
    wcel
    @2
    xrge0cmn
    @1
    cmnmnd
    ax-mp
    @3
    @1
    cpo
    wcel
    @6
    @5
    @4
    cle
    wbr
    #
    wo
    #
    vy
    @0
    wral
    vx
    @0
    wral
    vx
    vy
    vz
    @0
    @1
    cle
    cxrs
    @0
    cress
    ovex
    xrge0base
    xrge0le
    @4
    @0
    wcel
    #
    @4
    cxr
    wcel
    #
    @4
    @4
    cle
    wbr
    @0
    cxr
    @4
    cc0
    cpnf
    iccssxr
    #
    sseli
    #
    @4
    xrleid
    syl
    @12
    @13
    @5
    cxr
    wcel
    #
    @6
    @10
    wa
    #
    @4
    @5
    wceq
    #
    wi
    @5
    @0
    wcel
    #
    @15
    @0
    cxr
    @5
    @14
    sseli
    #
    @13
    @16
    wa
    @18
    @17
    @4
    @5
    xrletri3
    biimprd
    syl2an
    @12
    @13
    @19
    @16
    @7
    @0
    wcel
    #
    @7
    cxr
    wcel
    #
    @6
    @5
    @7
    cle
    wbr
    wa
    @4
    @7
    cle
    wbr
    wi
    @15
    @20
    @0
    cxr
    @7
    @14
    sseli
    #
    @4
    @5
    @7
    xrletr
    syl3an
    isposi
    @11
    vx
    vy
    @0
    @12
    @13
    @16
    @11
    @19
    @15
    @20
    @4
    @5
    xrletri
    syl2an
    rgen2a
    vx
    vy
    @0
    @1
    cle
    xrge0base
    xrge0le
    istos
    mpbir2an
    @9
    vx
    vy
    vz
    @0
    @0
    @0
    @12
    @13
    @19
    @16
    @21
    @22
    @9
    @15
    @20
    @23
    @13
    @16
    @22
    w3a
    @6
    @8
    @4
    @5
    @7
    xleadd1a
    ex
    syl3an
    rgen3
    @0
    cxad
    cle
    @1
    vx
    vy
    vz
    xrge0base
    xrge0plusg
    xrge0le
    isomnd
    mpbir3an
end
