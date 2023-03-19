include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cprmo.mm"
include "cfv.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "c1.mm"
include "cgcd.mm"
include "clt.mm"
include "cle.mm"
include "w3a.mm"
include "cprime.mm"
include "prmuz2.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "anbi12d.mm"
include "adantl.mm"
include "pm3.22.mm"
include "3adant1.mm"
include "rspcedvd.mm"
include "prmdvdsprmop.mm"
include "r19.29a.mm"
include "cn0.mm"
include "nnnn0.mm"
include "prmocl.mm"
include "syl.mm"
include "elfzuz.mm"
include "eluz2nn.mm"
include "nnaddcl.mm"
include "syl2an.mm"
include "ncoprmgcdgt1b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem prmgapprmolem
  let cI: class I
  let cN: class N
  let vp: setvar p
  let vq: setvar q


  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> 1 < ( ( ( #p ` N ) + I ) gcd I ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c2
    cN
    cfz
    co
    wcel
    #
    wa
    #
    vq
    cv
    #
    cN
    cprmo
    cfv
    #
    cI
    caddc
    co
    #
    cdvds
    wbr
    #
    @3
    cI
    cdvds
    wbr
    #
    wa
    #
    vq
    c2
    cuz
    cfv
    #
    wrex
    #
    c1
    @5
    cI
    cgcd
    co
    clt
    wbr
    #
    @2
    vp
    cv
    #
    cN
    cle
    wbr
    #
    @12
    cI
    cdvds
    wbr
    #
    @12
    @5
    cdvds
    wbr
    #
    w3a
    #
    @10
    vp
    cprime
    @2
    @12
    cprime
    wcel
    #
    wa
    #
    @16
    wa
    #
    @8
    @15
    @14
    wa
    #
    vq
    @12
    @9
    @17
    @12
    @9
    wcel
    @2
    @16
    @12
    prmuz2
    ad2antlr
    @3
    @12
    wceq
    #
    @8
    @20
    wb
    @19
    @21
    @6
    @15
    @7
    @14
    @3
    @12
    @5
    cdvds
    breq1
    @3
    @12
    cI
    cdvds
    breq1
    anbi12d
    adantl
    @16
    @20
    @18
    @14
    @15
    @20
    @13
    @14
    @15
    pm3.22
    3adant1
    adantl
    rspcedvd
    cI
    cN
    vp
    prmdvdsprmop
    r19.29a
    @2
    @5
    cn
    wcel
    #
    cI
    cn
    wcel
    #
    @10
    @11
    wb
    @0
    @4
    cn
    wcel
    #
    @23
    @22
    @1
    @0
    cN
    cn0
    wcel
    @24
    cN
    nnnn0
    cN
    prmocl
    syl
    @1
    cI
    @9
    wcel
    @23
    cI
    c2
    cN
    elfzuz
    cI
    eluz2nn
    syl
    #
    @4
    cI
    nnaddcl
    syl2an
    @1
    @23
    @0
    @25
    adantl
    @5
    cI
    vq
    ncoprmgcdgt1b
    syl2anc
    mpbid
end
