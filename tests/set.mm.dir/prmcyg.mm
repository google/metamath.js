include "cgrp.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cprime.mm"
include "wa.mm"
include "cv.mm"
include "c0g.mm"
include "csn.mm"
include "wn.mm"
include "ccyg.mm"
include "wss.mm"
include "wex.mm"
include "c1.mm"
include "1nprm.mm"
include "simpr.mm"
include "eqid.mm"
include "grpidcl.mm"
include "snssd.mm"
include "ad2antrr.mm"
include "eqssd.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "mtoi.mm"
include "nss.mm"
include "sylib.mm"
include "cod.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "wb.mm"
include "odeq1.mm"
include "syl2anc.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "mtbird.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "cfn.mm"
include "cn0.mm"
include "cn.mm"
include "prmnn.mm"
include "ad2antlr.mm"
include "nnnn0d.mm"
include "cbs.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "sylibr.mm"
include "oddvds2.mm"
include "syl3anc.mm"
include "odcl2.mm"
include "dvdsprime.mm"
include "mpbid.mm"
include "ord.mm"
include "mt3d.mm"
include "iscygodd.mm"
include "exlimddv.mm"

theorem prmcyg
  let cB: class B
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )


  assert |- ( ( G e. Grp /\ ( # ` B ) e. Prime ) -> G e. CycGrp )

  proof
    cG
    cgrp
    wcel
    #
    cB
    chash
    cfv
    #
    cprime
    wcel
    #
    wa
    #
    vx
    cv
    #
    cB
    wcel
    #
    @4
    cG
    c0g
    cfv
    #
    csn
    #
    wcel
    #
    wn
    #
    wa
    #
    cG
    ccyg
    wcel
    vx
    @3
    cB
    @7
    wss
    #
    wn
    @10
    vx
    wex
    @3
    @11
    c1
    cprime
    wcel
    #
    1nprm
    @3
    @11
    @12
    @3
    @11
    wa
    #
    @1
    c1
    cprime
    @13
    @1
    @7
    chash
    cfv
    #
    c1
    @13
    cB
    @7
    chash
    @13
    cB
    @7
    @3
    @11
    simpr
    @0
    @7
    cB
    wss
    @2
    @11
    @0
    @6
    cB
    cB
    cG
    @6
    cygctb.1
    @6
    eqid
    #
    grpidcl
    snssd
    ad2antrr
    eqssd
    fveq2d
    @6
    cvv
    wcel
    @14
    c1
    wceq
    cG
    c0g
    fvex
    @6
    cvv
    hashsng
    ax-mp
    syl6eq
    @0
    @2
    @11
    simplr
    eqeltrrd
    ex
    mtoi
    vx
    cB
    @7
    nss
    sylib
    @3
    @10
    wa
    #
    cB
    cG
    cG
    cod
    cfv
    #
    @4
    cygctb.1
    @17
    eqid
    #
    @0
    @2
    @10
    simpll
    #
    @3
    @5
    @9
    simprl
    #
    @16
    @4
    @17
    cfv
    #
    @1
    wceq
    #
    @21
    c1
    wceq
    #
    @16
    @23
    @8
    @3
    @5
    @9
    simprr
    @16
    @23
    @4
    @6
    wceq
    #
    @8
    @16
    @0
    @5
    @23
    @24
    wb
    @19
    @20
    @4
    cG
    @17
    cB
    @6
    @18
    @15
    cygctb.1
    odeq1
    syl2anc
    vx
    @6
    velsn
    syl6bbr
    mtbird
    @16
    @22
    @23
    @16
    @21
    @1
    cdvds
    wbr
    #
    @22
    @23
    wo
    #
    @16
    @0
    cB
    cfn
    wcel
    #
    @5
    @25
    @19
    @16
    @1
    cn0
    wcel
    #
    @27
    @16
    @1
    @2
    @1
    cn
    wcel
    @0
    @10
    @1
    prmnn
    ad2antlr
    nnnn0d
    cB
    cvv
    wcel
    @27
    @28
    wb
    cB
    cG
    cbs
    cfv
    cvv
    cygctb.1
    cG
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashclb
    ax-mp
    sylibr
    #
    @20
    @4
    cG
    @17
    cB
    cygctb.1
    @18
    oddvds2
    syl3anc
    @16
    @2
    @21
    cn
    wcel
    #
    @25
    @26
    wb
    @0
    @2
    @10
    simplr
    @16
    @0
    @27
    @5
    @30
    @19
    @29
    @20
    @4
    cG
    @17
    cB
    cygctb.1
    @18
    odcl2
    syl3anc
    @1
    @21
    dvdsprime
    syl2anc
    mpbid
    ord
    mt3d
    iscygodd
    exlimddv
end
