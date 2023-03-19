include "c0v.mm"
include "csn.mm"
include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "chil.mm"
include "wss.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "ax-hv0cl.mm"
include "snssi.mm"
include "ax-mp.mm"
include "elexi.mm"
include "snid.mm"
include "pm3.2i.mm"
include "wceq.mm"
include "velsn.mm"
include "oveq12.mm"
include "hvaddid2i.mm"
include "syl6eq.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "oveq2.mm"
include "hvmul0.mm"
include "sylan9eqr.mm"
include "sylan2b.mm"
include "rgen2.mm"
include "issh2.mm"
include "mpbir2an.mm"
include "wb.mm"
include "cxp.mm"
include "fconst2.mm"
include "hlim0.mm"
include "breq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "hlimuni.mm"
include "eleq1d.mm"
include "sylan.mm"
include "mpbii.mm"
include "gen2.mm"
include "isch2.mm"

theorem hsn0elch
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- { 0h } e. CH

  proof
    c0v
    csn
    #
    cch
    wcel
    @0
    csh
    wcel
    #
    cn
    @0
    vf
    cv
    #
    wf
    #
    @2
    vx
    cv
    #
    chli
    wbr
    #
    wa
    #
    @4
    @0
    wcel
    #
    wi
    #
    vx
    wal
    vf
    wal
    @1
    @0
    chil
    wss
    #
    c0v
    @0
    wcel
    #
    wa
    @4
    vy
    cv
    #
    cva
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @4
    @11
    csm
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    cc
    wral
    #
    wa
    @9
    @10
    c0v
    chil
    wcel
    @9
    ax-hv0cl
    c0v
    chil
    snssi
    ax-mp
    c0v
    c0v
    chil
    ax-hv0cl
    elexi
    #
    snid
    #
    pm3.2i
    @14
    @17
    @13
    vx
    vy
    @0
    @7
    @4
    c0v
    wceq
    #
    @11
    c0v
    wceq
    #
    @13
    @11
    @0
    wcel
    #
    vx
    c0v
    velsn
    vy
    c0v
    velsn
    #
    @20
    @21
    wa
    #
    @12
    c0v
    wceq
    @13
    @24
    @12
    c0v
    c0v
    cva
    co
    c0v
    @4
    c0v
    @11
    c0v
    cva
    oveq12
    c0v
    ax-hv0cl
    hvaddid2i
    syl6eq
    @12
    c0v
    @4
    @11
    cva
    ovex
    elsn
    sylibr
    syl2anb
    rgen2a
    @16
    vx
    vy
    cc
    @0
    @22
    @4
    cc
    wcel
    #
    @21
    @16
    @23
    @25
    @21
    wa
    @15
    c0v
    wceq
    @16
    @21
    @25
    @15
    @4
    c0v
    csm
    co
    c0v
    @11
    c0v
    @4
    csm
    oveq2
    @4
    hvmul0
    sylan9eqr
    @15
    c0v
    @4
    @11
    csm
    ovex
    elsn
    sylibr
    sylan2b
    rgen2
    pm3.2i
    vx
    vy
    @0
    issh2
    mpbir2an
    @8
    vf
    vx
    @6
    @10
    @7
    @19
    @3
    @2
    c0v
    chli
    wbr
    #
    @5
    @10
    @7
    wb
    @3
    @2
    cn
    @0
    cxp
    #
    wceq
    #
    @26
    cn
    c0v
    @2
    @18
    fconst2
    @28
    @26
    @27
    c0v
    chli
    wbr
    hlim0
    @2
    @27
    c0v
    chli
    breq1
    mpbiri
    sylbi
    @26
    @5
    wa
    c0v
    @4
    @0
    c0v
    @4
    @2
    hlimuni
    eleq1d
    sylan
    mpbii
    gen2
    vx
    vf
    @0
    isch2
    mpbir2an
end
