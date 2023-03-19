include "cvc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cgi.mm"
include "cfv.mm"
include "cgr.mm"
include "wceq.mm"
include "vcgrp.mm"
include "adantr.mm"
include "cc.mm"
include "neg1cn.mm"
include "vccl.mm"
include "mp3an2.mm"
include "eqid.mm"
include "grporid.mm"
include "syl2anc.mm"
include "simpr.mm"
include "grpoinvcl.mm"
include "sylan.mm"
include "grpoass.mm"
include "syl13anc.mm"
include "vcidOLD.mm"
include "oveq2d.mm"
include "caddc.mm"
include "cc0.mm"
include "ax-1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "oveq1i.mm"
include "vcdir.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "vc0.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "grporinv.mm"
include "grpolid.mm"

theorem vcm
  let cA: class A
  let cS: class S
  let cG: class G
  let cM: class M
  let cW: class W
  let cX: class X
  assume vcm.1: |- G = ( 1st ` W )
  assume vcm.2: |- S = ( 2nd ` W )
  assume vcm.3: |- X = ran G
  assume vcm.4: |- M = ( inv ` G )


  assert |- ( ( W e. CVecOLD /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) )

  proof
    cW
    cvc
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cA
    cS
    co
    #
    cG
    cgi
    cfv
    #
    cG
    co
    #
    @4
    cA
    cM
    cfv
    #
    @2
    cG
    cgr
    wcel
    #
    @4
    cX
    wcel
    #
    @6
    @4
    wceq
    @0
    @8
    @1
    cG
    cW
    vcm.1
    vcgrp
    #
    adantr
    #
    @0
    @3
    cc
    wcel
    #
    @1
    @9
    neg1cn
    @3
    cA
    cS
    cG
    cW
    cX
    vcm.1
    vcm.2
    vcm.3
    vccl
    mp3an2
    #
    @4
    @5
    cG
    cX
    vcm.3
    @5
    eqid
    #
    grporid
    syl2anc
    @2
    @5
    @7
    cG
    co
    #
    @6
    @7
    @2
    @4
    cA
    @7
    cG
    co
    #
    cG
    co
    #
    @15
    @6
    @2
    @4
    cA
    cG
    co
    #
    @7
    cG
    co
    #
    @17
    @15
    @2
    @8
    @9
    @1
    @7
    cX
    wcel
    #
    @19
    @17
    wceq
    @11
    @13
    @0
    @1
    simpr
    @0
    @8
    @1
    @20
    @10
    cA
    cG
    cM
    cX
    vcm.3
    vcm.4
    grpoinvcl
    sylan
    #
    @4
    cA
    @7
    cG
    cX
    vcm.3
    grpoass
    syl13anc
    @2
    @18
    @5
    @7
    cG
    @2
    @4
    c1
    cA
    cS
    co
    #
    cG
    co
    #
    @18
    @5
    @2
    @22
    cA
    @4
    cG
    cA
    cS
    cG
    cW
    cX
    vcm.1
    vcm.2
    vcm.3
    vcidOLD
    oveq2d
    @2
    @3
    c1
    caddc
    co
    #
    cA
    cS
    co
    #
    cc0
    cA
    cS
    co
    @23
    @5
    @24
    cc0
    cA
    cS
    c1
    @3
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    oveq1i
    @0
    c1
    cc
    wcel
    #
    @1
    @25
    @23
    wceq
    #
    ax-1cn
    @0
    @12
    @26
    @1
    @27
    neg1cn
    @3
    c1
    cA
    cS
    cG
    cW
    cX
    vcm.1
    vcm.2
    vcm.3
    vcdir
    mp3anr1
    mpanr1
    cA
    cS
    cG
    cW
    cX
    @5
    vcm.1
    vcm.2
    vcm.3
    @14
    vc0
    3eqtr3a
    eqtr3d
    oveq1d
    eqtr3d
    @2
    @16
    @5
    @4
    cG
    @0
    @8
    @1
    @16
    @5
    wceq
    @10
    cA
    @5
    cG
    cM
    cX
    vcm.3
    @14
    vcm.4
    grporinv
    sylan
    oveq2d
    eqtr3d
    @2
    @8
    @20
    @15
    @7
    wceq
    @11
    @21
    @7
    @5
    cG
    cX
    vcm.3
    @14
    grpolid
    syl2anc
    eqtr3d
    eqtr3d
end
