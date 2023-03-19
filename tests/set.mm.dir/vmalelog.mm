include "cn.mm"
include "wcel.mm"
include "cvma.mm"
include "cfv.mm"
include "clog.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "breq1.mm"
include "wne.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cprime.mm"
include "isppw2.mm"
include "wa.mm"
include "cmul.mm"
include "crp.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "adantr.mm"
include "relogcld.mm"
include "cr.mm"
include "nnre.mm"
include "adantl.mm"
include "c1.mm"
include "log1.mm"
include "nnge1d.mm"
include "wb.mm"
include "1rp.mm"
include "logleb.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "nnge1.mm"
include "lemulge12d.mm"
include "vmappw.mm"
include "cz.mm"
include "nnz.mm"
include "relogexp.mm"
include "syl2an.mm"
include "3brtr4d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl6bi.mm"
include "imp.mm"
include "nnrp.mm"
include "pm2.61ne.mm"

theorem vmalelog
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( A e. NN -> ( Lam ` A ) <_ ( log ` A ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cvma
    cfv
    #
    cA
    clog
    cfv
    #
    cle
    wbr
    #
    cc0
    @2
    cle
    wbr
    @1
    cc0
    @1
    cc0
    @2
    cle
    breq1
    @0
    @1
    cc0
    wne
    #
    @3
    @0
    @4
    cA
    vp
    cv
    #
    vk
    cv
    #
    cexp
    co
    #
    wceq
    #
    vk
    cn
    wrex
    vp
    cprime
    wrex
    @3
    cA
    vk
    vp
    isppw2
    @8
    @3
    vp
    vk
    cprime
    cn
    @5
    cprime
    wcel
    #
    @6
    cn
    wcel
    #
    wa
    #
    @3
    @8
    @7
    cvma
    cfv
    #
    @7
    clog
    cfv
    #
    cle
    wbr
    @11
    @5
    clog
    cfv
    #
    @6
    @14
    cmul
    co
    #
    @12
    @13
    cle
    @11
    @14
    @6
    @11
    @5
    @9
    @5
    crp
    wcel
    #
    @10
    @9
    @5
    @5
    prmnn
    #
    nnrpd
    #
    adantr
    #
    relogcld
    @10
    @6
    cr
    wcel
    @9
    @6
    nnre
    adantl
    @11
    cc0
    c1
    clog
    cfv
    #
    @14
    cle
    log1
    @11
    c1
    @5
    cle
    wbr
    #
    @20
    @14
    cle
    wbr
    #
    @11
    @5
    @9
    @5
    cn
    wcel
    @10
    @17
    adantr
    nnge1d
    @11
    c1
    crp
    wcel
    #
    @16
    @21
    @22
    wb
    1rp
    @19
    c1
    @5
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @10
    c1
    @6
    cle
    wbr
    @9
    @6
    nnge1
    adantl
    lemulge12d
    @5
    @6
    vmappw
    @9
    @16
    @6
    cz
    wcel
    @13
    @15
    wceq
    @10
    @18
    @6
    nnz
    @5
    @6
    relogexp
    syl2an
    3brtr4d
    @8
    @1
    @12
    @2
    @13
    cle
    cA
    @7
    cvma
    fveq2
    cA
    @7
    clog
    fveq2
    breq12d
    syl5ibrcom
    rexlimivv
    syl6bi
    imp
    @0
    cc0
    @20
    @2
    cle
    log1
    @0
    c1
    cA
    cle
    wbr
    #
    @20
    @2
    cle
    wbr
    #
    cA
    nnge1
    @0
    @23
    cA
    crp
    wcel
    @24
    @25
    wb
    1rp
    cA
    nnrp
    c1
    cA
    logleb
    sylancr
    mpbid
    syl5eqbrr
    pm2.61ne
end
