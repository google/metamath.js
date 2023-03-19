include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmt.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "ngpgrp.mm"
include "ngpms.mm"
include "ngprcan.mm"
include "ralrimivvva.mm"
include "3jca.mm"
include "csg.mm"
include "cfv.mm"
include "cnm.mm"
include "simp1.mm"
include "simp2.mm"
include "wa.mm"
include "cminusg.mm"
include "wi.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "ad2ant2rl.mm"
include "eqcom.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "rspcv.mm"
include "syl.mm"
include "c0g.mm"
include "grpsubval.mm"
include "adantl.mm"
include "eqcomd.mm"
include "grprinv.mm"
include "grpsubcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "nmval.mm"
include "eqtr4d.mm"
include "sylibd.mm"
include "ralimdvva.mm"
include "3impia.mm"
include "isngp3.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem isngp4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let c.pl: class .+
  let cG: class G
  let cX: class X
  assume ngprcan.x: |- X = ( Base ` G )
  assume ngprcan.p: |- .+ = ( +g ` G )
  assume ngprcan.d: |- D = ( dist ` G )

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint .+ z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( G e. NrmGrp <-> ( G e. Grp /\ G e. MetSp /\ A. x e. X A. y e. X A. z e. X ( ( x .+ z ) D ( y .+ z ) ) = ( x D y ) ) )

  proof
    cG
    cngp
    wcel
    #
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    #
    vx
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    vy
    cv
    #
    @4
    c.pl
    co
    #
    cD
    co
    #
    @3
    @6
    cD
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    w3a
    #
    @0
    @1
    @2
    @12
    cG
    ngpgrp
    cG
    ngpms
    @0
    @10
    vx
    vy
    vz
    cX
    cX
    cX
    @3
    @6
    @4
    cD
    c.pl
    cG
    cX
    ngprcan.x
    ngprcan.p
    ngprcan.d
    ngprcan
    ralrimivvva
    3jca
    @13
    @1
    @2
    @9
    @3
    @6
    cG
    csg
    cfv
    #
    co
    #
    cG
    cnm
    cfv
    #
    cfv
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @0
    @1
    @2
    @12
    simp1
    @1
    @2
    @12
    simp2
    @1
    @2
    @12
    @19
    @1
    @2
    wa
    #
    @11
    @18
    vx
    vy
    cX
    cX
    @20
    @3
    cX
    wcel
    #
    @6
    cX
    wcel
    #
    wa
    #
    wa
    #
    @11
    @9
    @3
    @6
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @6
    @26
    c.pl
    co
    #
    cD
    co
    #
    wceq
    #
    @18
    @24
    @26
    cX
    wcel
    #
    @11
    @30
    wi
    @1
    @22
    @31
    @2
    @21
    cX
    cG
    @25
    @6
    ngprcan.x
    @25
    eqid
    #
    grpinvcl
    ad2ant2rl
    @10
    @30
    vz
    @26
    cX
    @10
    @9
    @8
    wceq
    @4
    @26
    wceq
    #
    @30
    @8
    @9
    eqcom
    @33
    @8
    @29
    @9
    @33
    @5
    @27
    @7
    @28
    cD
    @4
    @26
    @3
    c.pl
    oveq2
    @4
    @26
    @6
    c.pl
    oveq2
    oveq12d
    eqeq2d
    syl5bb
    rspcv
    syl
    @24
    @29
    @17
    @9
    @24
    @29
    @15
    cG
    c0g
    cfv
    #
    cD
    co
    #
    @17
    @24
    @27
    @15
    @28
    @34
    cD
    @24
    @15
    @27
    @23
    @15
    @27
    wceq
    @20
    cX
    c.pl
    cG
    @25
    @14
    @3
    @6
    ngprcan.x
    ngprcan.p
    @32
    @14
    eqid
    #
    grpsubval
    adantl
    eqcomd
    @1
    @22
    @28
    @34
    wceq
    @2
    @21
    cX
    c.pl
    cG
    @25
    @6
    @34
    ngprcan.x
    ngprcan.p
    @34
    eqid
    #
    @32
    grprinv
    ad2ant2rl
    oveq12d
    @24
    @15
    cX
    wcel
    #
    @17
    @35
    wceq
    @1
    @23
    @38
    @2
    @1
    @21
    @22
    @38
    cX
    cG
    @14
    @3
    @6
    ngprcan.x
    @36
    grpsubcl
    3expb
    adantlr
    @15
    cD
    @16
    cG
    cX
    @34
    @16
    eqid
    #
    ngprcan.x
    @37
    ngprcan.d
    nmval
    syl
    eqtr4d
    eqeq2d
    sylibd
    ralimdvva
    3impia
    vx
    vy
    cD
    cG
    @14
    @16
    cX
    @39
    @36
    ngprcan.d
    ngprcan.x
    isngp3
    syl3anbrc
    impbii
end
