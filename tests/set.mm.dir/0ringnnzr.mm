include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "cnzr.mm"
include "1re.mm"
include "ltnri.mm"
include "breq2.mm"
include "mtbiri.mm"
include "adantl.mm"
include "intnand.mm"
include "ex.mm"
include "wo.mm"
include "wi.mm"
include "ianor.mm"
include "pm2.21.mm"
include "cle.mm"
include "cxr.mm"
include "wb.mm"
include "cvv.mm"
include "fvex.mm"
include "hashxrcl.mm"
include "ax-mp.mm"
include "rexri.mm"
include "xrlenlt.mm"
include "mp2an.mm"
include "bicomi.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "cn.mm"
include "cfn.mm"
include "cn0.mm"
include "a1i.mm"
include "1nn0.mm"
include "hashbnd.mm"
include "syl3anc.mm"
include "hashcl.mm"
include "cc0.mm"
include "hasheq0.mm"
include "syl.mm"
include "biimpd.mm"
include "necon3d.mm"
include "impcom.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "adantr.mm"
include "com12.mm"
include "mpcom.mm"
include "nnle1eq1.mm"
include "mpbid.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpbn0.mm"
include "syl11.mm"
include "sylbi.mm"
include "jaoi.mm"
include "impbid.mm"
include "isnzr2hash.mm"
include "notbii.mm"
include "syl6bb.mm"

theorem 0ringnnzr
  let cR: class R


  assert |- ( R e. Ring -> ( ( # ` ( Base ` R ) ) = 1 <-> -. R e. NzRing ) )

  proof
    cR
    crg
    wcel
    #
    cR
    cbs
    cfv
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @0
    c1
    @2
    clt
    wbr
    #
    wa
    #
    wn
    #
    cR
    cnzr
    wcel
    #
    wn
    @0
    @3
    @6
    @0
    @3
    @6
    @0
    @3
    wa
    @4
    @0
    @3
    @4
    wn
    #
    @0
    @3
    @4
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @2
    c1
    c1
    clt
    breq2
    mtbiri
    adantl
    intnand
    ex
    @6
    @0
    @3
    @6
    @0
    wn
    #
    @8
    wo
    @0
    @3
    wi
    #
    @0
    @4
    ianor
    @9
    @10
    @8
    @0
    @3
    pm2.21
    @8
    @2
    c1
    cle
    wbr
    #
    @10
    @11
    @8
    @2
    cxr
    wcel
    #
    c1
    cxr
    wcel
    @11
    @8
    wb
    @1
    cvv
    wcel
    #
    @12
    cR
    cbs
    fvex
    #
    @1
    cvv
    hashxrcl
    ax-mp
    c1
    1re
    rexri
    @2
    c1
    xrlenlt
    mp2an
    bicomi
    @1
    c0
    wne
    #
    @11
    @3
    @0
    @15
    @11
    @3
    @15
    @11
    wa
    #
    @11
    @3
    @15
    @11
    simpr
    #
    @16
    @2
    cn
    wcel
    #
    @11
    @3
    wb
    @1
    cfn
    wcel
    #
    @16
    @18
    @16
    @13
    c1
    cn0
    wcel
    #
    @11
    @19
    @13
    @16
    @14
    a1i
    @20
    @16
    1nn0
    a1i
    @17
    @1
    c1
    cvv
    hashbnd
    syl3anc
    @19
    @2
    cn0
    wcel
    #
    @16
    @18
    wi
    @1
    hashcl
    @16
    @21
    @18
    @15
    @21
    @18
    wi
    @11
    @15
    @21
    @18
    @15
    @21
    wa
    @21
    @2
    cc0
    wne
    #
    @18
    @15
    @21
    simpr
    @21
    @15
    @22
    @21
    @2
    cc0
    @1
    c0
    @21
    @2
    cc0
    wceq
    #
    @1
    c0
    wceq
    #
    @21
    @13
    @23
    @24
    wb
    @13
    @21
    @14
    a1i
    @1
    cvv
    hasheq0
    syl
    biimpd
    necon3d
    impcom
    @2
    elnnne0
    sylanbrc
    ex
    adantr
    com12
    syl
    mpcom
    @2
    nnle1eq1
    syl
    mpbid
    ex
    @0
    cR
    cgrp
    wcel
    @15
    cR
    ringgrp
    @1
    cR
    @1
    eqid
    #
    grpbn0
    syl
    syl11
    sylbi
    jaoi
    sylbi
    com12
    impbid
    @5
    @7
    @7
    @5
    @1
    cR
    @25
    isnzr2hash
    bicomi
    notbii
    syl6bb
end
