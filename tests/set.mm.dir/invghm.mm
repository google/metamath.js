include "cabl.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "ablgrp.mm"
include "cgrp.mm"
include "wf.mm"
include "grpinvf.mm"
include "syl.mm"
include "cv.mm"
include "wceq.mm"
include "ablinvadd.mm"
include "3expb.mm"
include "isghmd.mm"
include "wral.mm"
include "ghmgrp1.mm"
include "wa.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "grpinvadd.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "simpl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ghmlin.mm"
include "grpinvinv.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "grpcl.mm"
include "eqtr3d.mm"
include "ralrimivva.mm"
include "isabl2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem invghm
  let cB: class B
  let cG: class G
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume invghm.b: |- B = ( Base ` G )
  assume invghm.m: |- I = ( invg ` G )


  assert |- ( G e. Abel <-> I e. ( G GrpHom G ) )

  proof
    cG
    cabl
    wcel
    #
    cI
    cG
    cG
    cghm
    co
    wcel
    #
    @0
    vx
    vy
    cG
    cplusg
    cfv
    #
    @2
    cG
    cG
    cI
    cB
    cB
    invghm.b
    invghm.b
    @2
    eqid
    #
    @3
    cG
    ablgrp
    #
    @4
    @0
    cG
    cgrp
    wcel
    #
    cB
    cB
    cI
    wf
    @4
    cB
    cG
    cI
    invghm.b
    invghm.m
    grpinvf
    syl
    @0
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    @6
    @8
    @2
    co
    #
    cI
    cfv
    @6
    cI
    cfv
    #
    @8
    cI
    cfv
    #
    @2
    co
    #
    wceq
    cB
    @2
    cG
    cI
    @6
    @8
    invghm.b
    @3
    invghm.m
    ablinvadd
    3expb
    isghmd
    @1
    @5
    @10
    @8
    @6
    @2
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @0
    cG
    cG
    cI
    ghmgrp1
    #
    @1
    @15
    vx
    vy
    cB
    cB
    @1
    @7
    @9
    wa
    #
    wa
    #
    @14
    cI
    cfv
    #
    cI
    cfv
    #
    @10
    @14
    @18
    @20
    @13
    cI
    cfv
    #
    @11
    cI
    cfv
    #
    @12
    cI
    cfv
    #
    @2
    co
    #
    @10
    @18
    @19
    @13
    cI
    @18
    @5
    @9
    @7
    @19
    @13
    wceq
    @1
    @5
    @17
    @16
    adantr
    #
    @1
    @7
    @9
    simprr
    #
    @1
    @7
    @9
    simprl
    #
    cB
    @2
    cG
    cI
    @8
    @6
    invghm.b
    @3
    invghm.m
    grpinvadd
    syl3anc
    fveq2d
    @18
    @1
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @21
    @24
    wceq
    @1
    @17
    simpl
    @18
    @5
    @7
    @28
    @25
    @27
    cB
    cG
    cI
    @6
    invghm.b
    invghm.m
    grpinvcl
    syl2anc
    @18
    @5
    @9
    @29
    @25
    @26
    cB
    cG
    cI
    @8
    invghm.b
    invghm.m
    grpinvcl
    syl2anc
    @2
    @2
    cG
    cG
    @11
    cI
    @12
    cB
    invghm.b
    @3
    @3
    ghmlin
    syl3anc
    @18
    @22
    @6
    @23
    @8
    @2
    @18
    @5
    @7
    @22
    @6
    wceq
    @25
    @27
    cB
    cG
    cI
    @6
    invghm.b
    invghm.m
    grpinvinv
    syl2anc
    @18
    @5
    @9
    @23
    @8
    wceq
    @25
    @26
    cB
    cG
    cI
    @8
    invghm.b
    invghm.m
    grpinvinv
    syl2anc
    oveq12d
    3eqtrd
    @18
    @5
    @14
    cB
    wcel
    #
    @20
    @14
    wceq
    @25
    @18
    @5
    @9
    @7
    @30
    @25
    @26
    @27
    cB
    @2
    cG
    @8
    @6
    invghm.b
    @3
    grpcl
    syl3anc
    cB
    cG
    cI
    @14
    invghm.b
    invghm.m
    grpinvinv
    syl2anc
    eqtr3d
    ralrimivva
    vx
    vy
    cB
    @2
    cG
    invghm.b
    @3
    isabl2
    sylanbrc
    impbii
end
