include "zring.mm"
include "clpir.mm"
include "wcel.mm"
include "crg.mm"
include "clidl.mm"
include "cfv.mm"
include "clpidl.mm"
include "wss.mm"
include "zringring.mm"
include "cv.mm"
include "cc0.mm"
include "csn.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cn.mm"
include "cin.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "zringlpirlem2.mm"
include "simpll.mm"
include "simplr.mm"
include "zringlpirlem3.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "dvdsrzring.mm"
include "lpigen.mm"
include "mpan.mm"
include "adantr.mm"
include "mpbird.mm"
include "zring0.mm"
include "lpi0.mm"
include "mp1i.mm"
include "pm2.61ne.mm"
include "ssriv.mm"
include "islpir2.mm"
include "mpbir2an.mm"

theorem zringlpir
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ZZring e. LPIR

  proof
    zring
    clpir
    wcel
    zring
    crg
    wcel
    #
    zring
    clidl
    cfv
    #
    zring
    clpidl
    cfv
    #
    wss
    zringring
    vx
    @1
    @2
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    cc0
    csn
    #
    @2
    wcel
    #
    @3
    @6
    @3
    @6
    @2
    eleq1
    @4
    @3
    @6
    wne
    #
    wa
    #
    @5
    vy
    cv
    #
    vz
    cv
    #
    cdvds
    wbr
    #
    vz
    @3
    wral
    #
    vy
    @3
    wrex
    #
    @9
    @3
    cn
    cin
    cr
    clt
    cinf
    #
    @3
    wcel
    @15
    @11
    cdvds
    wbr
    #
    vz
    @3
    wral
    #
    @14
    @9
    @15
    @3
    @4
    @8
    simpl
    @4
    @8
    simpr
    @15
    eqid
    #
    zringlpirlem2
    @9
    @16
    vz
    @3
    @9
    @11
    @3
    wcel
    #
    wa
    @15
    @3
    @11
    @4
    @8
    @19
    simpll
    @4
    @8
    @19
    simplr
    @18
    @9
    @19
    simpr
    zringlpirlem3
    ralrimiva
    @13
    @17
    vy
    @15
    @3
    @10
    @15
    wceq
    @12
    @16
    vz
    @3
    @10
    @15
    @11
    cdvds
    breq1
    ralbidv
    rspcev
    syl2anc
    @4
    @5
    @14
    wb
    #
    @8
    @0
    @4
    @20
    zringring
    vy
    vz
    cdvds
    @2
    zring
    @1
    @3
    @1
    eqid
    #
    @2
    eqid
    #
    dvdsrzring
    lpigen
    mpan
    adantr
    mpbird
    @0
    @7
    @4
    zringring
    @2
    zring
    cc0
    @22
    zring0
    lpi0
    mp1i
    pm2.61ne
    ssriv
    @2
    zring
    @1
    @22
    @21
    islpir2
    mpbir2an
end
