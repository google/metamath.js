include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "wo.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "elznn0.mm"
include "c1.mm"
include "caddc.mm"
include "nn0p1nn.mm"
include "adantl.mm"
include "1nn.mm"
include "a1i.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "negsub.mm"
include "sylancr.mm"
include "simpr.mm"
include "nnnn0addcl.mm"
include "eqeltrrd.mm"
include "nncan.mm"
include "jaodan.mm"
include "nnre.mm"
include "resubcl.mm"
include "syl2an.mm"
include "cle.mm"
include "wbr.mm"
include "letric.mm"
include "syl2anr.mm"
include "wb.mm"
include "nnnn0.mm"
include "nn0sub.mm"
include "nncn.mm"
include "negsubdi2.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "orbi12d.mm"
include "mpbid.mm"
include "jca.mm"
include "eleq1.mm"
include "negeq.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "impbii.mm"
include "bitri.mm"

theorem elz2
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let vz: setvar z

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint x z
  disjoint y z
  disjoint N z
  assert |- ( N e. ZZ <-> E. x e. NN E. y e. NN N = ( x - y ) )

  proof
    cN
    cz
    wcel
    cN
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    #
    cN
    vx
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cn
    wrex
    #
    cN
    elznn0
    @5
    @10
    @0
    @1
    @10
    @3
    @0
    @1
    wa
    #
    cN
    c1
    caddc
    co
    #
    cn
    wcel
    #
    c1
    cn
    wcel
    #
    cN
    @12
    c1
    cmin
    co
    #
    wceq
    @10
    @1
    @13
    @0
    cN
    nn0p1nn
    adantl
    @14
    @11
    1nn
    a1i
    @11
    @15
    cN
    @11
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @15
    cN
    wceq
    @0
    @16
    @1
    cN
    recn
    #
    adantr
    ax-1cn
    cN
    c1
    pncan
    sylancl
    eqcomd
    vx
    vy
    cn
    cn
    @12
    c1
    cN
    cmin
    rspceov
    syl3anc
    @0
    @3
    wa
    #
    @14
    c1
    cN
    cmin
    co
    #
    cn
    wcel
    cN
    c1
    @20
    cmin
    co
    #
    wceq
    @10
    @14
    @19
    1nn
    a1i
    @19
    c1
    @2
    caddc
    co
    #
    @20
    cn
    @19
    @17
    @16
    @22
    @20
    wceq
    ax-1cn
    @0
    @16
    @3
    @18
    adantr
    #
    c1
    cN
    negsub
    sylancr
    @19
    @14
    @3
    @22
    cn
    wcel
    1nn
    @0
    @3
    simpr
    c1
    @2
    nnnn0addcl
    sylancr
    eqeltrrd
    @19
    @21
    cN
    @19
    @17
    @16
    @21
    cN
    wceq
    ax-1cn
    @23
    c1
    cN
    nncan
    sylancr
    eqcomd
    vx
    vy
    cn
    cn
    c1
    @20
    cN
    cmin
    rspceov
    syl3anc
    jaodan
    @9
    @5
    vx
    vy
    cn
    cn
    @6
    cn
    wcel
    #
    @7
    cn
    wcel
    #
    wa
    #
    @5
    @9
    @8
    cr
    wcel
    #
    @8
    cn0
    wcel
    #
    @8
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    @26
    @27
    @31
    @24
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @27
    @25
    @6
    nnre
    #
    @7
    nnre
    #
    @6
    @7
    resubcl
    syl2an
    @26
    @7
    @6
    cle
    wbr
    #
    @6
    @7
    cle
    wbr
    #
    wo
    #
    @31
    @25
    @33
    @32
    @38
    @24
    @35
    @34
    @7
    @6
    letric
    syl2anr
    @26
    @36
    @28
    @37
    @30
    @25
    @7
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    @36
    @28
    wb
    @24
    @7
    nnnn0
    #
    @6
    nnnn0
    #
    @7
    @6
    nn0sub
    syl2anr
    @26
    @37
    @7
    @6
    cmin
    co
    #
    cn0
    wcel
    #
    @30
    @24
    @40
    @39
    @37
    @44
    wb
    @25
    @42
    @41
    @6
    @7
    nn0sub
    syl2an
    @26
    @29
    @43
    cn0
    @24
    @6
    cc
    wcel
    @7
    cc
    wcel
    @29
    @43
    wceq
    @25
    @6
    nncn
    @7
    nncn
    @6
    @7
    negsubdi2
    syl2an
    eleq1d
    bitr4d
    orbi12d
    mpbid
    jca
    @9
    @0
    @27
    @4
    @31
    cN
    @8
    cr
    eleq1
    @9
    @1
    @28
    @3
    @30
    cN
    @8
    cn0
    eleq1
    @9
    @2
    @29
    cn0
    cN
    @8
    negeq
    eleq1d
    orbi12d
    anbi12d
    syl5ibrcom
    rexlimivv
    impbii
    bitri
end
