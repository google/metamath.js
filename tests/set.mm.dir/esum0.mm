include "wcel.mm"
include "cc0.mm"
include "cesum.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "nfel1.mm"
include "id.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "cxrs.mm"
include "cress.mm"
include "cgsu.mm"
include "wceq.mm"
include "cmnd.mm"
include "cvv.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "ax-mp.mm"
include "vex.mm"
include "xrge00.mm"
include "gsumz.mm"
include "mp2an.mm"
include "esumval.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "eqcomi.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wral.mm"
include "0xr.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "ne0ii.mm"
include "fconst5.mm"
include "mpbi.mm"
include "supeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "supsn.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem esum0
  let cA: class A
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume esum0.k: |- F/_ k A

  disjoint V k
  disjoint A x
  disjoint k x
  disjoint V x
  assert |- ( A e. V -> sum* k e. A 0 = 0 )

  proof
    cA
    cV
    wcel
    #
    cA
    cc0
    vk
    cesum
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    cc0
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    @0
    vx
    cA
    cc0
    cc0
    vk
    cV
    vk
    cA
    cV
    esum0.k
    nfel1
    esum0.k
    @0
    id
    cc0
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @0
    vk
    cv
    cA
    wcel
    wa
    0e0iccpnf
    a1i
    cxrs
    @6
    cress
    co
    #
    vk
    vx
    cv
    #
    cc0
    cmpt
    cgsu
    co
    cc0
    wceq
    #
    @0
    @8
    @2
    wcel
    wa
    @7
    cmnd
    wcel
    #
    @8
    cvv
    wcel
    @9
    @7
    ccmn
    wcel
    @10
    xrge0cmn
    @7
    cmnmnd
    ax-mp
    vx
    vex
    @8
    vk
    @7
    cvv
    cc0
    xrge00
    gsumz
    mp2an
    a1i
    esumval
    @0
    @5
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    @0
    cxr
    @4
    @11
    clt
    @4
    @11
    wceq
    #
    @0
    @3
    @2
    @11
    cxp
    #
    wceq
    #
    @13
    @14
    @3
    vx
    @2
    cc0
    fconstmpt
    eqcomi
    @3
    @2
    wfn
    #
    @2
    c0
    wne
    @15
    @13
    wb
    cc0
    cxr
    wcel
    #
    vx
    @2
    wral
    @16
    @17
    vx
    @2
    0xr
    rgenw
    vx
    @2
    cc0
    @3
    cxr
    @3
    eqid
    fnmpt
    ax-mp
    c0
    @2
    c0
    @2
    wcel
    c0
    @1
    wcel
    c0
    cfn
    wcel
    cA
    0elpw
    0fin
    c0
    @1
    cfn
    elin
    mpbir2an
    ne0ii
    @2
    cc0
    @3
    fconst5
    mp2an
    mpbi
    a1i
    supeq1d
    cxr
    clt
    wor
    @17
    @12
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    syl6eq
    eqtrd
end
