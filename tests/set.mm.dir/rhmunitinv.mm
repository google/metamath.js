include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "wa.mm"
include "cinvr.mm"
include "cmulr.mm"
include "wceq.mm"
include "cur.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "eqid.mm"
include "unitlinv.mm"
include "sylan.mm"
include "fveq2d.mm"
include "cbs.mm"
include "simpl.mm"
include "unitss.mm"
include "unitinvcl.mm"
include "sseldi.mm"
include "simpr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "rhm1.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "rhmrcl2.mm"
include "elrhmunit.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "cmgp.mm"
include "cress.mm"
include "cgrp.mm"
include "wb.mm"
include "unitgrp.mm"
include "syl.mm"
include "syldan.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem rhmunitinv
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( F e. ( R RingHom S ) /\ A e. ( Unit ` R ) ) -> ( F ` ( ( invr ` R ) ` A ) ) = ( ( invr ` S ) ` ( F ` A ) ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cR
    cui
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cR
    cinvr
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @7
    cS
    cinvr
    cfv
    #
    cfv
    #
    @7
    @8
    co
    #
    wceq
    #
    @6
    @11
    wceq
    #
    @3
    @9
    cS
    cur
    cfv
    #
    @12
    @3
    @5
    cA
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    cR
    cur
    cfv
    #
    cF
    cfv
    #
    @9
    @15
    @3
    @17
    @19
    cF
    @0
    cR
    crg
    wcel
    #
    @2
    @17
    @19
    wceq
    cR
    cS
    cF
    rhmrcl1
    #
    cR
    @16
    @1
    @19
    @4
    cA
    @1
    eqid
    #
    @4
    eqid
    #
    @16
    eqid
    #
    @19
    eqid
    #
    unitlinv
    sylan
    fveq2d
    @3
    @0
    @5
    cR
    cbs
    cfv
    #
    wcel
    cA
    @27
    wcel
    @18
    @9
    wceq
    @0
    @2
    simpl
    @3
    @1
    @27
    @5
    @27
    cR
    @1
    @27
    eqid
    #
    @23
    unitss
    #
    @0
    @21
    @2
    @5
    @1
    wcel
    #
    @22
    cR
    @1
    @4
    cA
    @23
    @24
    unitinvcl
    sylan
    #
    sseldi
    @3
    @1
    @27
    cA
    @29
    @0
    @2
    simpr
    sseldi
    @5
    cA
    cR
    cS
    @16
    @8
    cF
    @27
    @28
    @25
    @8
    eqid
    #
    rhmmul
    syl3anc
    @0
    @20
    @15
    wceq
    @2
    cR
    cS
    @19
    cF
    @15
    @26
    @15
    eqid
    #
    rhm1
    adantr
    3eqtr3d
    @3
    cS
    crg
    wcel
    #
    @7
    cS
    cui
    cfv
    #
    wcel
    #
    @12
    @15
    wceq
    @0
    @34
    @2
    cR
    cS
    cF
    rhmrcl2
    #
    adantr
    #
    cA
    cR
    cS
    cF
    elrhmunit
    #
    cS
    @8
    @35
    @15
    @10
    @7
    @35
    eqid
    #
    @10
    eqid
    #
    @32
    @33
    unitlinv
    syl2anc
    eqtr4d
    @3
    cS
    cmgp
    cfv
    #
    @35
    cress
    co
    #
    cgrp
    wcel
    #
    @6
    @35
    wcel
    #
    @11
    @35
    wcel
    #
    @36
    @13
    @14
    wb
    @0
    @44
    @2
    @0
    @34
    @44
    @37
    cS
    @35
    @43
    @40
    @43
    eqid
    #
    unitgrp
    syl
    adantr
    @0
    @2
    @30
    @45
    @31
    @5
    cR
    cS
    cF
    elrhmunit
    syldan
    @3
    @34
    @36
    @46
    @38
    @39
    cS
    @35
    @10
    @7
    @40
    @41
    unitinvcl
    syl2anc
    @39
    @35
    @8
    @43
    @6
    @11
    @7
    cS
    @35
    @43
    @40
    @47
    unitgrpbas
    @35
    cvv
    wcel
    @8
    @43
    cplusg
    cfv
    wceq
    cS
    cui
    fvex
    @35
    @8
    @42
    @43
    cvv
    @47
    cS
    @8
    @42
    @42
    eqid
    @32
    mgpplusg
    ressplusg
    ax-mp
    grprcan
    syl13anc
    mpbid
end
