include "cm1r.mm"
include "cplr.mm"
include "co.mm"
include "cltr.mm"
include "wbr.mm"
include "cv.mm"
include "c1p.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "wceq.mm"
include "cnp.mm"
include "wrex.mm"
include "cnr.mm"
include "wcel.mm"
include "ltrelsr.mm"
include "brel.mm"
include "simprd.mm"
include "cmr.mm"
include "wb.mm"
include "ltasr.mm"
include "ax-mp.mm"
include "c0r.mm"
include "pn0sr.mm"
include "oveq1i.mm"
include "addasssr.mm"
include "addcomsr.mm"
include "3eqtr3i.mm"
include "0idsr.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "syl5bb.mm"
include "wi.mm"
include "m1r.mm"
include "mulclsr.mm"
include "mp2an.mm"
include "addclsr.mm"
include "mpan.mm"
include "df-nr.mm"
include "breq2.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "wa.mm"
include "cpp.mm"
include "cltp.mm"
include "df-m1r.mm"
include "breq1i.mm"
include "addasspr.mm"
include "breq2i.mm"
include "ltsrpr.mm"
include "1pr.mm"
include "ltapr.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "ltexpri.mm"
include "sylbi.mm"
include "enreceq.mm"
include "mpanl2.mm"
include "addcompr.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"
include "ancoms.mm"
include "rexbidva.mm"
include "syl5ibr.mm"
include "ecoptocl.mm"
include "syl.mm"
include "oveq2.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "reximdv.mm"
include "syld.mm"
include "sylbird.mm"
include "mpcom.mm"
include "mappsrpr.mm"
include "syl5bbr.mm"
include "biimpac.mm"
include "rexlimiva.mm"
include "impbii.mm"

theorem map2psrpr
  let vx: setvar x
  let cA: class A
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  assume map2psrpr.2: |- C e. R.

  disjoint A x
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C y
  disjoint C z
  assert |- ( ( C +R -1R ) <R A <-> E. x e. P. ( C +R [ <. x , 1P >. ] ~R ) = A )

  proof
    cC
    cm1r
    cplr
    co
    #
    cA
    cltr
    wbr
    #
    cC
    vx
    cv
    #
    c1p
    cop
    cer
    cec
    #
    cplr
    co
    #
    cA
    wceq
    #
    vx
    cnp
    wrex
    #
    cA
    cnr
    wcel
    #
    @1
    @6
    @1
    @0
    cnr
    wcel
    @7
    @0
    cA
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simprd
    @7
    @1
    cm1r
    cC
    cm1r
    cmr
    co
    #
    cA
    cplr
    co
    #
    cltr
    wbr
    #
    @6
    @10
    @0
    cC
    @9
    cplr
    co
    #
    cltr
    wbr
    #
    @7
    @1
    cC
    cnr
    wcel
    #
    @10
    @12
    wb
    map2psrpr.2
    cm1r
    @9
    cC
    ltasr
    ax-mp
    @7
    @11
    cA
    @0
    cltr
    @7
    @11
    cA
    c0r
    cplr
    co
    #
    cA
    cC
    @8
    cplr
    co
    #
    cA
    cplr
    co
    c0r
    cA
    cplr
    co
    @11
    @14
    @15
    c0r
    cA
    cplr
    @13
    @15
    c0r
    wceq
    map2psrpr.2
    cC
    pn0sr
    ax-mp
    oveq1i
    cC
    @8
    cA
    addasssr
    c0r
    cA
    addcomsr
    3eqtr3i
    cA
    0idsr
    syl5eq
    #
    breq2d
    syl5bb
    @7
    @10
    @3
    @9
    wceq
    #
    vx
    cnp
    wrex
    #
    @6
    @7
    @9
    cnr
    wcel
    #
    @10
    @18
    wi
    #
    @8
    cnr
    wcel
    #
    @7
    @19
    @13
    cm1r
    cnr
    wcel
    @21
    map2psrpr.2
    m1r
    cC
    cm1r
    mulclsr
    mp2an
    @8
    cA
    addclsr
    mpan
    cm1r
    vy
    cv
    #
    vz
    cv
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    @3
    @24
    wceq
    #
    vx
    cnp
    wrex
    #
    wi
    @20
    vy
    vz
    @9
    cnp
    cnp
    cer
    cnr
    df-nr
    @24
    @9
    wceq
    #
    @25
    @10
    @27
    @18
    @24
    @9
    cm1r
    cltr
    breq2
    @28
    @26
    @17
    vx
    cnp
    @24
    @9
    @3
    eqeq2
    rexbidv
    imbi12d
    @25
    @27
    @22
    cnp
    wcel
    @23
    cnp
    wcel
    wa
    #
    @23
    @2
    cpp
    co
    #
    c1p
    @22
    cpp
    co
    #
    wceq
    #
    vx
    cnp
    wrex
    #
    @25
    @23
    @31
    cltp
    wbr
    #
    @33
    @25
    c1p
    c1p
    c1p
    cpp
    co
    #
    cop
    cer
    cec
    #
    @24
    cltr
    wbr
    #
    @34
    cm1r
    @36
    @24
    cltr
    df-m1r
    breq1i
    c1p
    @23
    cpp
    co
    #
    @35
    @22
    cpp
    co
    #
    cltp
    wbr
    @38
    c1p
    @31
    cpp
    co
    #
    cltp
    wbr
    #
    @37
    @34
    @39
    @40
    @38
    cltp
    c1p
    c1p
    @22
    addasspr
    breq2i
    c1p
    @35
    @22
    @23
    ltsrpr
    c1p
    cnp
    wcel
    #
    @34
    @41
    wb
    1pr
    @23
    @31
    c1p
    ltapr
    ax-mp
    3bitr4i
    bitri
    vx
    @23
    @31
    ltexpri
    sylbi
    @29
    @26
    @32
    vx
    cnp
    @2
    cnp
    wcel
    #
    @29
    @26
    @32
    wb
    @43
    @29
    wa
    @26
    @2
    @23
    cpp
    co
    #
    @31
    wceq
    #
    @32
    @43
    @42
    @29
    @26
    @45
    wb
    1pr
    @2
    c1p
    @22
    @23
    enreceq
    mpanl2
    @30
    @44
    @31
    @23
    @2
    addcompr
    eqeq1i
    syl6bbr
    ancoms
    rexbidva
    syl5ibr
    ecoptocl
    syl
    @7
    @17
    @5
    vx
    cnp
    @7
    @17
    @5
    @17
    @7
    @4
    @11
    cA
    @3
    @9
    cC
    cplr
    oveq2
    @16
    sylan9eqr
    ex
    reximdv
    syld
    sylbird
    mpcom
    @5
    @1
    vx
    cnp
    @5
    @43
    @1
    @43
    @0
    @4
    cltr
    wbr
    @5
    @1
    @2
    cC
    map2psrpr.2
    mappsrpr
    @4
    cA
    @0
    cltr
    breq2
    syl5bbr
    biimpac
    rexlimiva
    impbii
end
