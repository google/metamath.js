include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "co.mm"
include "mulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "fmptd.mm"
include "adantr.mm"
include "cmin.mm"
include "wb.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "cdvds.mm"
include "wbr.mm"
include "simplr.mm"
include "breq1d.mm"
include "c0g.mm"
include "eqid.mm"
include "odcong.mm"
include "adantlr.mm"
include "zsubcl.mm"
include "0dvds.mm"
include "syl.mm"
include "3bitr3d.mm"
include "cc.mm"
include "zcn.mm"
include "subeq0.mm"
include "syl2an.mm"
include "3bitrd.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "odid.mm"
include "mulg0.mm"
include "eqtr4d.mm"
include "ad2antlr.mm"
include "cn0.mm"
include "odcl.mm"
include "nn0zd.mm"
include "0zd.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "impbida.mm"

theorem odf1
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume odf1.1: |- X = ( Base ` G )
  assume odf1.2: |- O = ( od ` G )
  assume odf1.3: |- .x. = ( .g ` G )
  assume odf1.4: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint O x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G y
  disjoint G z
  disjoint O y
  disjoint O z
  disjoint .x. y
  disjoint .x. z
  disjoint X y
  disjoint X z
  disjoint F y
  disjoint F z
  assert |- ( ( G e. Grp /\ A e. X ) -> ( ( O ` A ) = 0 <-> F : ZZ -1-1-> X ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    #
    cc0
    wceq
    #
    cz
    cX
    cF
    wf1
    #
    @2
    @4
    wa
    #
    cz
    cX
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @8
    @10
    wceq
    #
    wi
    #
    vz
    cz
    wral
    vy
    cz
    wral
    @5
    @2
    @7
    @4
    @2
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cX
    cF
    @0
    @15
    cz
    wcel
    #
    @1
    @16
    cX
    wcel
    #
    @0
    @17
    @1
    @18
    cX
    c.x
    cG
    @15
    cA
    odf1.1
    odf1.3
    mulgcl
    3expa
    an32s
    odf1.4
    fmptd
    adantr
    @6
    @14
    vy
    vz
    cz
    cz
    @6
    @8
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    wa
    #
    wa
    #
    @12
    @13
    @22
    @12
    @8
    cA
    c.x
    co
    #
    @10
    cA
    c.x
    co
    #
    wceq
    #
    @8
    @10
    cmin
    co
    #
    cc0
    wceq
    #
    @13
    @21
    @12
    @25
    wb
    @6
    @19
    @20
    @9
    @23
    @11
    @24
    vx
    @8
    @16
    @23
    cz
    cF
    @15
    @8
    cA
    c.x
    oveq1
    odf1.4
    @15
    cA
    c.x
    ovex
    #
    fvmpt3i
    vx
    @10
    @16
    @24
    cz
    cF
    @15
    @10
    cA
    c.x
    oveq1
    odf1.4
    @28
    fvmpt3i
    eqeqan12d
    adantl
    @22
    @3
    @26
    cdvds
    wbr
    #
    cc0
    @26
    cdvds
    wbr
    #
    @25
    @27
    @22
    @3
    cc0
    @26
    cdvds
    @2
    @4
    @21
    simplr
    breq1d
    @2
    @21
    @29
    @25
    wb
    #
    @4
    @0
    @1
    @21
    @31
    cA
    c.x
    cG
    @8
    @10
    cO
    cX
    cG
    c0g
    cfv
    #
    odf1.1
    odf1.2
    odf1.3
    @32
    eqid
    #
    odcong
    3expa
    adantlr
    @22
    @26
    cz
    wcel
    #
    @30
    @27
    wb
    @21
    @34
    @6
    @8
    @10
    zsubcl
    adantl
    @26
    0dvds
    syl
    3bitr3d
    @21
    @27
    @13
    wb
    #
    @6
    @19
    @8
    cc
    wcel
    @10
    cc
    wcel
    @35
    @20
    @8
    zcn
    @10
    zcn
    @8
    @10
    subeq0
    syl2an
    adantl
    3bitrd
    biimpd
    ralrimivva
    vy
    vz
    cz
    cX
    cF
    dff13
    sylanbrc
    @2
    @5
    wa
    #
    @3
    cF
    cfv
    #
    cc0
    cF
    cfv
    #
    wceq
    #
    @4
    @36
    @3
    cA
    c.x
    co
    #
    cc0
    cA
    c.x
    co
    #
    @37
    @38
    @1
    @40
    @41
    wceq
    @0
    @5
    @1
    @40
    @32
    @41
    cA
    c.x
    cG
    cO
    cX
    @32
    odf1.1
    odf1.2
    odf1.3
    @33
    odid
    cX
    c.x
    cG
    cA
    @32
    odf1.1
    @33
    odf1.3
    mulg0
    eqtr4d
    ad2antlr
    @36
    @3
    cz
    wcel
    #
    @37
    @40
    wceq
    @36
    @3
    @1
    @3
    cn0
    wcel
    @0
    @5
    cA
    cG
    cO
    cX
    odf1.1
    odf1.2
    odcl
    ad2antlr
    nn0zd
    #
    vx
    @3
    @16
    @40
    cz
    cF
    @15
    @3
    cA
    c.x
    oveq1
    odf1.4
    @28
    fvmpt3i
    syl
    @36
    cc0
    cz
    wcel
    #
    @38
    @41
    wceq
    @36
    0zd
    #
    vx
    cc0
    @16
    @41
    cz
    cF
    @15
    cc0
    cA
    c.x
    oveq1
    odf1.4
    @28
    fvmpt3i
    syl
    3eqtr4d
    @36
    @5
    @42
    @44
    @39
    @4
    wb
    @2
    @5
    simpr
    @43
    @45
    cz
    cX
    @3
    cc0
    cF
    f1fveq
    syl12anc
    mpbid
    impbida
end
