include "crp.mm"
include "wcel.mm"
include "cpnf.mm"
include "cxdiv.mm"
include "co.mm"
include "cv.mm"
include "cxmu.mm"
include "wceq.mm"
include "cxr.mm"
include "crio.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "rprene0.mm"
include "pnfxr.mm"
include "jctil.mm"
include "3anass.mm"
include "sylibr.mm"
include "xdivval.mm"
include "syl.mm"
include "a1i.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "xlemul2.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "clt.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "xmulpnf1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "breq1d.mm"
include "bitr2d.mm"
include "xmulcl.mm"
include "sylan.mm"
include "xgepnf.mm"
include "adantl.mm"
include "3bitr3d.mm"
include "riota5.mm"
include "eqtrd.mm"

theorem xdivpnfrp
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR+ -> ( +oo /e A ) = +oo )

  proof
    cA
    crp
    wcel
    #
    cpnf
    cA
    cxdiv
    co
    #
    cA
    vx
    cv
    #
    cxmu
    co
    #
    cpnf
    wceq
    #
    vx
    cxr
    crio
    #
    cpnf
    @0
    cpnf
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    w3a
    #
    @1
    @5
    wceq
    @0
    @6
    @7
    @8
    wa
    #
    wa
    @9
    @0
    @10
    @6
    cA
    rprene0
    pnfxr
    jctil
    @6
    @7
    @8
    3anass
    sylibr
    vx
    cpnf
    cA
    xdivval
    syl
    @0
    @4
    vx
    cxr
    cpnf
    @6
    @0
    pnfxr
    a1i
    @0
    @2
    cxr
    wcel
    #
    wa
    #
    cpnf
    @3
    cle
    wbr
    #
    cpnf
    @2
    cle
    wbr
    #
    @4
    @2
    cpnf
    wceq
    #
    @12
    @14
    cA
    cpnf
    cxmu
    co
    #
    @3
    cle
    wbr
    #
    @13
    @11
    @0
    @14
    @17
    wb
    #
    @6
    @11
    @0
    @18
    pnfxr
    cpnf
    @2
    cA
    xlemul2
    mp3an1
    ancoms
    @12
    @16
    cpnf
    @3
    cle
    @0
    @16
    cpnf
    wceq
    #
    @11
    @0
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    @19
    cA
    rpxr
    #
    cA
    rpgt0
    cA
    xmulpnf1
    syl2anc
    adantr
    breq1d
    bitr2d
    @12
    @3
    cxr
    wcel
    #
    @13
    @4
    wb
    @0
    @20
    @11
    @22
    @21
    cA
    @2
    xmulcl
    sylan
    @3
    xgepnf
    syl
    @11
    @14
    @15
    wb
    @0
    @2
    xgepnf
    adantl
    3bitr3d
    riota5
    eqtrd
end
