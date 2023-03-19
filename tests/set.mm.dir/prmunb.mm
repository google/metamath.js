include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "nnnn0.mm"
include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdvds.mm"
include "c2.mm"
include "cuz.mm"
include "faccl.mm"
include "elnnuz.mm"
include "eluzp1p1.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "sylbi.mm"
include "exprmfct.mm"
include "3syl.mm"
include "wa.mm"
include "cle.mm"
include "wn.mm"
include "wi.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "nn0z.mm"
include "eluz.mm"
include "syl2an.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "adantr.mm"
include "simpld.mm"
include "nnnn0d.mm"
include "eluznn0.mm"
include "sylancom.mm"
include "nnz.mm"
include "simprd.mm"
include "dvdsfac.mm"
include "w3a.mm"
include "ndvdsp1.mm"
include "imp.mm"
include "syl31anc.mm"
include "ex.mm"
include "sylbird.mm"
include "con2d.mm"
include "ancoms.mm"
include "cr.mm"
include "nn0re.mm"
include "zred.mm"
include "ltnle.mm"
include "sylibrd.mm"
include "reximdva.mm"
include "mpd.mm"
include "syl.mm"

theorem prmunb
  let cN: class N
  let vp: setvar p

  disjoint N p
  assert |- ( N e. NN -> E. p e. Prime N < p )

  proof
    cN
    cn
    wcel
    cN
    cn0
    wcel
    #
    cN
    vp
    cv
    #
    clt
    wbr
    #
    vp
    cprime
    wrex
    #
    cN
    nnnn0
    @0
    @1
    cN
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @3
    @0
    @4
    cn
    wcel
    #
    @5
    c2
    cuz
    cfv
    #
    wcel
    #
    @7
    cN
    faccl
    #
    @8
    @4
    c1
    cuz
    cfv
    wcel
    #
    @10
    @4
    elnnuz
    @12
    @5
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    @9
    c1
    @4
    eluzp1p1
    c2
    @13
    cuz
    df-2
    fveq2i
    syl6eleqr
    sylbi
    @5
    vp
    exprmfct
    3syl
    @0
    @6
    @2
    vp
    cprime
    @0
    @1
    cprime
    wcel
    #
    wa
    @6
    @1
    cN
    cle
    wbr
    #
    wn
    #
    @2
    @14
    @0
    @6
    @16
    wi
    @14
    @0
    wa
    #
    @15
    @6
    @17
    @15
    cN
    @1
    cuz
    cfv
    wcel
    #
    @6
    wn
    #
    @14
    @1
    cz
    wcel
    cN
    cz
    wcel
    @18
    @15
    wb
    @0
    @1
    prmz
    #
    cN
    nn0z
    @1
    cN
    eluz
    syl2an
    @14
    @18
    @19
    wi
    @0
    @14
    @18
    @19
    @14
    @18
    wa
    #
    @4
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    c1
    @1
    clt
    wbr
    #
    @1
    @4
    cdvds
    wbr
    #
    @19
    @21
    @0
    @8
    @22
    @14
    @18
    @1
    cn0
    wcel
    @0
    @21
    @1
    @21
    @23
    @24
    @14
    @23
    @24
    wa
    #
    @18
    @14
    @1
    @9
    wcel
    @26
    @1
    prmuz2
    @1
    eluz2b2
    sylib
    adantr
    #
    simpld
    #
    nnnn0d
    cN
    @1
    eluznn0
    sylancom
    @11
    @4
    nnz
    3syl
    @28
    @21
    @23
    @24
    @27
    simprd
    @14
    @18
    @23
    @25
    @28
    @1
    cN
    dvdsfac
    sylancom
    @22
    @23
    @24
    w3a
    @25
    @19
    @1
    @4
    ndvdsp1
    imp
    syl31anc
    ex
    adantr
    sylbird
    con2d
    ancoms
    @0
    cN
    cr
    wcel
    @1
    cr
    wcel
    @2
    @16
    wb
    @14
    cN
    nn0re
    @14
    @1
    @20
    zred
    cN
    @1
    ltnle
    syl2an
    sylibrd
    reximdva
    mpd
    syl
end
