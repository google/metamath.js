include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cif.mm"
include "csgn.mm"
include "cfv.mm"
include "recn.mm"
include "negeq0d.mm"
include "bicomd.mm"
include "wa.mm"
include "eqidd.mm"
include "wn.mm"
include "wne.mm"
include "necon3bbid.mm"
include "biimpa.mm"
include "wb.mm"
include "lt0neg2.mm"
include "adantr.mm"
include "wo.mm"
include "id.mm"
include "0red.mm"
include "lttri2d.mm"
include "ltnsym2.mm"
include "mpdan.mm"
include "jca.mm"
include "pm5.17.mm"
include "sylib.mm"
include "con2bid.mm"
include "bitr3d.mm"
include "ifbid.mm"
include "ifnot.mm"
include "syl6eq.mm"
include "syldan.mm"
include "ifbieq12d2.mm"
include "cxr.mm"
include "renegcl.mm"
include "rexr.mm"
include "sgnval.mm"
include "3syl.mm"
include "cmin.mm"
include "co.mm"
include "df-neg.mm"
include "a1i.mm"
include "syl.mm"
include "oveq2d.mm"
include "ovif2.mm"
include "biid.mm"
include "0m0e0.mm"
include "caddc.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "subnegi.mm"
include "0p1e1.mm"
include "eqtr2i.mm"
include "ifbieq12i.mm"
include "eqtr4i.mm"
include "eqtri.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem sgnneg
  let cA: class A


  assert |- ( A e. RR -> ( sgn ` -u A ) = -u ( sgn ` A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cc0
    wceq
    #
    cc0
    @1
    cc0
    clt
    wbr
    #
    c1
    cneg
    #
    c1
    cif
    #
    cif
    #
    cA
    cc0
    wceq
    #
    cc0
    cA
    cc0
    clt
    wbr
    #
    c1
    @4
    cif
    #
    cif
    #
    @1
    csgn
    cfv
    #
    cA
    csgn
    cfv
    #
    cneg
    #
    @0
    @2
    @7
    cc0
    @5
    cc0
    @9
    @0
    @7
    @2
    @0
    cA
    cA
    recn
    negeq0d
    bicomd
    #
    @0
    @2
    wa
    cc0
    eqidd
    @0
    @2
    wn
    #
    cA
    cc0
    wne
    #
    @5
    @9
    wceq
    @0
    @15
    @16
    @0
    @2
    cA
    cc0
    @14
    necon3bbid
    biimpa
    @0
    @16
    wa
    #
    @5
    @8
    wn
    #
    @4
    c1
    cif
    @9
    @17
    @3
    @18
    @4
    c1
    @17
    cc0
    cA
    clt
    wbr
    #
    @3
    @18
    @0
    @19
    @3
    wb
    @16
    cA
    lt0neg2
    adantr
    @17
    @8
    @19
    @17
    @8
    @19
    wo
    #
    @8
    @19
    wa
    wn
    #
    wa
    @8
    @19
    wn
    wb
    @17
    @20
    @21
    @0
    @16
    @20
    @0
    cA
    cc0
    @0
    id
    @0
    0red
    #
    lttri2d
    biimpa
    @0
    @21
    @16
    @0
    cc0
    cr
    wcel
    @21
    @22
    cA
    cc0
    ltnsym2
    mpdan
    adantr
    jca
    @8
    @19
    pm5.17
    sylib
    con2bid
    bitr3d
    ifbid
    @8
    @4
    c1
    ifnot
    syl6eq
    syldan
    ifbieq12d2
    @0
    @1
    cr
    wcel
    @1
    cxr
    wcel
    @11
    @6
    wceq
    cA
    renegcl
    @1
    rexr
    @1
    sgnval
    3syl
    @0
    @13
    cc0
    @12
    cmin
    co
    #
    cc0
    @7
    cc0
    @8
    @4
    c1
    cif
    #
    cif
    #
    cmin
    co
    #
    @10
    @13
    @23
    wceq
    @0
    @12
    df-neg
    a1i
    @0
    @12
    @25
    cc0
    cmin
    @0
    cA
    cxr
    wcel
    @12
    @25
    wceq
    cA
    rexr
    cA
    sgnval
    syl
    oveq2d
    @26
    @10
    wceq
    @0
    @26
    @7
    cc0
    cc0
    cmin
    co
    #
    cc0
    @24
    cmin
    co
    #
    cif
    @10
    @7
    cc0
    cc0
    @24
    cmin
    ovif2
    @7
    @7
    @27
    @28
    cc0
    @9
    @7
    biid
    0m0e0
    @28
    @8
    cc0
    @4
    cmin
    co
    #
    cc0
    c1
    cmin
    co
    #
    cif
    @9
    @8
    cc0
    @4
    c1
    cmin
    ovif2
    @8
    @8
    c1
    @4
    @29
    @30
    @8
    biid
    @29
    cc0
    c1
    caddc
    co
    c1
    cc0
    c1
    0cn
    ax-1cn
    subnegi
    0p1e1
    eqtr2i
    c1
    df-neg
    ifbieq12i
    eqtr4i
    ifbieq12i
    eqtri
    a1i
    3eqtrd
    3eqtr4d
end
