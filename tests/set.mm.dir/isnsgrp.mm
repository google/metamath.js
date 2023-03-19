include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "csgrp.mm"
include "wnel.mm"
include "wa.mm"
include "wn.mm"
include "cmgm.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "simpl1.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "notbid.mm"
include "rexbidv.mm"
include "adantl.mm"
include "simpl2.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "simpl3.mm"
include "neneq.mm"
include "rspcedvd.mm"
include "rexnal.mm"
include "2rexbii.mm"
include "rexnal2.mm"
include "bitr2i.mm"
include "sylibr.mm"
include "intnand.mm"
include "issgrp.mm"
include "sylnibr.mm"
include "df-nel.mm"
include "ex.mm"

theorem isnsgrp
  let cB: class B
  let cM: class M
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume issgrpn0.b: |- B = ( Base ` M )
  assume issgrpn0.o: |- .o. = ( +g ` M )


  assert |- ( ( X e. B /\ Y e. B /\ Z e. B ) -> ( ( ( X .o. Y ) .o. Z ) =/= ( X .o. ( Y .o. Z ) ) -> M e/ SGrp ) )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.op
    co
    #
    cZ
    c.op
    co
    #
    cX
    cY
    cZ
    c.op
    co
    #
    c.op
    co
    #
    wne
    #
    cM
    csgrp
    wnel
    #
    @3
    @8
    wa
    #
    cM
    csgrp
    wcel
    #
    wn
    @9
    @10
    cM
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    #
    vz
    cv
    #
    c.op
    co
    #
    @13
    @14
    @16
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    @11
    @10
    @22
    @12
    @10
    @20
    wn
    #
    vz
    cB
    wrex
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wrex
    #
    @22
    wn
    #
    @10
    @25
    cX
    @14
    c.op
    co
    #
    @16
    c.op
    co
    #
    cX
    @18
    c.op
    co
    #
    wceq
    #
    wn
    #
    vz
    cB
    wrex
    #
    vy
    cB
    wrex
    #
    vx
    cX
    cB
    @0
    @1
    @2
    @8
    simpl1
    @13
    cX
    wceq
    #
    @25
    @34
    wb
    @10
    @35
    @24
    @33
    vy
    cB
    @35
    @23
    @32
    vz
    cB
    @35
    @20
    @31
    @35
    @17
    @29
    @19
    @30
    @35
    @15
    @28
    @16
    c.op
    @13
    cX
    @14
    c.op
    oveq1
    oveq1d
    @13
    cX
    @18
    c.op
    oveq1
    eqeq12d
    notbid
    rexbidv
    rexbidv
    adantl
    @10
    @33
    @4
    @16
    c.op
    co
    #
    cX
    cY
    @16
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    wn
    #
    vz
    cB
    wrex
    vy
    cY
    cB
    @0
    @1
    @2
    @8
    simpl2
    @10
    @14
    cY
    wceq
    #
    wa
    @32
    @40
    vz
    cB
    @41
    @32
    @40
    wb
    @10
    @41
    @31
    @39
    @41
    @29
    @36
    @30
    @38
    @41
    @28
    @4
    @16
    c.op
    @14
    cY
    cX
    c.op
    oveq2
    oveq1d
    @41
    @18
    @37
    cX
    c.op
    @14
    cY
    @16
    c.op
    oveq1
    oveq2d
    eqeq12d
    notbid
    adantl
    rexbidv
    @10
    @40
    @5
    @7
    wceq
    #
    wn
    #
    vz
    cZ
    cB
    @0
    @1
    @2
    @8
    simpl3
    @16
    cZ
    wceq
    #
    @40
    @43
    wb
    @10
    @44
    @39
    @42
    @44
    @36
    @5
    @38
    @7
    @16
    cZ
    @4
    c.op
    oveq2
    @44
    @37
    @6
    cX
    c.op
    @16
    cZ
    cY
    c.op
    oveq2
    oveq2d
    eqeq12d
    notbid
    adantl
    @8
    @43
    @3
    @5
    @7
    neneq
    adantl
    rspcedvd
    rspcedvd
    rspcedvd
    @26
    @21
    wn
    #
    vy
    cB
    wrex
    vx
    cB
    wrex
    @27
    @24
    @45
    vx
    vy
    cB
    cB
    @20
    vz
    cB
    rexnal
    2rexbii
    @21
    vx
    vy
    cB
    cB
    rexnal2
    bitr2i
    sylibr
    intnand
    vx
    vy
    vz
    cB
    cM
    c.op
    issgrpn0.b
    issgrpn0.o
    issgrp
    sylnibr
    cM
    csgrp
    df-nel
    sylibr
    ex
end
