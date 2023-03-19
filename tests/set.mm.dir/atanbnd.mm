include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "catan.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "atanre.mm"
include "adantr.mm"
include "atanneg.mm"
include "syl.mm"
include "crp.mm"
include "renegcl.mm"
include "lt0neg1.mm"
include "biimpa.mm"
include "elrpd.mm"
include "atanbndlem.mm"
include "eqeltrrd.mm"
include "halfpire.mm"
include "recni.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "wb.mm"
include "neghalfpire.mm"
include "a1i.mm"
include "atanrecl.mm"
include "iooneg.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "simpr.mm"
include "fveq2d.mm"
include "atan0.mm"
include "syl6eq.mm"
include "0re.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpgt0.mm"
include "mp2b.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "cxr.mm"
include "w3a.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "syl6eqel.mm"
include "elrp.mm"
include "sylbir.mm"
include "w3o.mm"
include "lttri4.mm"
include "mpan2.mm"
include "mpjao3dan.mm"

theorem atanbnd
  let cA: class A


  assert |- ( A e. RR -> ( arctan ` A ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    cA
    catan
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @3
    cioo
    co
    #
    wcel
    #
    cA
    cc0
    wceq
    #
    cc0
    cA
    clt
    wbr
    #
    @0
    @1
    wa
    #
    @6
    @2
    cneg
    #
    @4
    @4
    cneg
    #
    cioo
    co
    #
    wcel
    #
    @9
    @10
    @5
    @12
    @9
    cA
    cneg
    #
    catan
    cfv
    #
    @10
    @5
    @9
    cA
    catan
    cdm
    wcel
    #
    @15
    @10
    wceq
    @0
    @16
    @1
    cA
    atanre
    adantr
    cA
    atanneg
    syl
    @9
    @14
    crp
    wcel
    @15
    @5
    wcel
    @9
    @14
    @0
    @14
    cr
    wcel
    @1
    cA
    renegcl
    adantr
    @0
    @1
    cc0
    @14
    clt
    wbr
    cA
    lt0neg1
    biimpa
    elrpd
    @14
    atanbndlem
    syl
    eqeltrrd
    @11
    @3
    @4
    cioo
    @3
    @3
    halfpire
    recni
    negnegi
    oveq2i
    syl6eleqr
    @9
    @4
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @6
    @13
    wb
    @17
    @9
    neghalfpire
    a1i
    @18
    @9
    halfpire
    a1i
    @0
    @19
    @1
    cA
    atanrecl
    adantr
    @4
    @3
    @2
    iooneg
    syl3anc
    mpbird
    @0
    @7
    wa
    #
    @2
    cc0
    @5
    @20
    @2
    cc0
    catan
    cfv
    cc0
    @20
    cA
    cc0
    catan
    @0
    @7
    simpr
    fveq2d
    atan0
    syl6eq
    cc0
    @5
    wcel
    #
    cc0
    cr
    wcel
    #
    @4
    cc0
    clt
    wbr
    #
    cc0
    @3
    clt
    wbr
    #
    0re
    @24
    @23
    cpi
    crp
    wcel
    @3
    crp
    wcel
    @24
    pirp
    cpi
    rphalfcl
    @3
    rpgt0
    mp2b
    #
    @18
    @24
    @23
    wb
    halfpire
    @3
    lt0neg2
    ax-mp
    mpbi
    @25
    @4
    cxr
    wcel
    @3
    cxr
    wcel
    @21
    @22
    @23
    @24
    w3a
    wb
    @4
    neghalfpire
    rexri
    @3
    halfpire
    rexri
    @4
    @3
    cc0
    elioo2
    mp2an
    mpbir3an
    syl6eqel
    @0
    @8
    wa
    cA
    crp
    wcel
    @6
    cA
    elrp
    cA
    atanbndlem
    sylbir
    @0
    @22
    @1
    @7
    @8
    w3o
    0re
    cA
    cc0
    lttri4
    mpan2
    mpjao3dan
end
