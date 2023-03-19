include "cgrp.mm"
include "wcel.mm"
include "cprime.mm"
include "cn0.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cod.mm"
include "wrex.mm"
include "wral.mm"
include "simpl2.mm"
include "simpl1.mm"
include "cdvds.mm"
include "simpll3.mm"
include "cfn.mm"
include "adantr.mm"
include "simplr.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "nnexpcld.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "simpr.mm"
include "eqid.mm"
include "oddvds2.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "odcl2.mm"
include "cpc.mm"
include "pcprmpw2.mm"
include "pcprmpw.mm"
include "bitr4d.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "ispgp.mm"
include "syl3anbrc.mm"
include "ex.mm"

theorem pgpfi1
  let cP: class P
  let cG: class G
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vx: setvar x
  assume pgpfi1.1: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ P e. Prime /\ N e. NN0 ) -> ( ( # ` X ) = ( P ^ N ) -> P pGrp G ) )

  proof
    cG
    cgrp
    wcel
    #
    cP
    cprime
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cX
    chash
    cfv
    #
    cP
    cN
    cexp
    co
    #
    wceq
    #
    cP
    cG
    cpgp
    wbr
    #
    @3
    @6
    wa
    #
    @1
    @0
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    vn
    cn0
    wrex
    #
    vx
    cX
    wral
    @7
    @0
    @1
    @2
    @6
    simpl2
    #
    @0
    @1
    @2
    @6
    simpl1
    #
    @8
    @14
    vx
    cX
    @8
    @9
    cX
    wcel
    #
    wa
    #
    @11
    @13
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @14
    @18
    @2
    @11
    @5
    cdvds
    wbr
    #
    @20
    @0
    @1
    @2
    @6
    @17
    simpll3
    #
    @18
    @11
    @4
    @5
    cdvds
    @18
    @0
    cX
    cfn
    wcel
    #
    @17
    @11
    @4
    cdvds
    wbr
    @8
    @0
    @17
    @16
    adantr
    #
    @18
    @4
    cn0
    wcel
    #
    @23
    @18
    @4
    @5
    cn0
    @3
    @6
    @17
    simplr
    #
    @18
    @5
    @18
    cP
    cN
    @18
    @1
    cP
    cn
    wcel
    @8
    @1
    @17
    @15
    adantr
    #
    cP
    prmnn
    syl
    @22
    nnexpcld
    nnnn0d
    eqeltrd
    cX
    cvv
    wcel
    @23
    @25
    wb
    cX
    cG
    cbs
    cfv
    cvv
    pgpfi1.1
    cG
    cbs
    fvex
    eqeltri
    cX
    cvv
    hashclb
    ax-mp
    sylibr
    #
    @8
    @17
    simpr
    #
    @9
    cG
    @10
    cX
    pgpfi1.1
    @10
    eqid
    #
    oddvds2
    syl3anc
    @26
    breqtrd
    @19
    @21
    vn
    cN
    cn0
    @12
    cN
    wceq
    @13
    @5
    @11
    cdvds
    @12
    cN
    cP
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    @18
    @1
    @11
    cn
    wcel
    #
    @20
    @14
    wb
    @27
    @18
    @0
    @23
    @17
    @31
    @24
    @28
    @29
    @9
    cG
    @10
    cX
    pgpfi1.1
    @30
    odcl2
    syl3anc
    @1
    @31
    wa
    @20
    @11
    cP
    cP
    @11
    cpc
    co
    cexp
    co
    wceq
    @14
    @11
    cP
    vn
    pcprmpw2
    @11
    cP
    vn
    pcprmpw
    bitr4d
    syl2anc
    mpbid
    ralrimiva
    vx
    cP
    vn
    cG
    @10
    cX
    pgpfi1.1
    @30
    ispgp
    syl3anbrc
    ex
end
