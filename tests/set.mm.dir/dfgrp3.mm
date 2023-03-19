include "cgrp.mm"
include "wcel.mm"
include "csgrp.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "grpsgrp.mm"
include "grpbn0.mm"
include "csg.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr.mm"
include "adantl.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "grpnpcan.mm"
include "rspcedvd.mm"
include "cminusg.mm"
include "grpinvcl.mm"
include "adantrr.mm"
include "grpcl.mm"
include "oveq2.mm"
include "c0g.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "grpass.mm"
include "syl13anc.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "mndlid.mm"
include "syl2an.mm"
include "3eqtr3d.mm"
include "jca.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "simp1.mm"
include "dfgrp3lem.mm"
include "dfgrp2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem dfgrp3
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let vr: setvar r
  let vl: setvar l
  let va: setvar a
  let vi: setvar i
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  assume dfgrp3.b: |- B = ( Base ` G )
  assume dfgrp3.p: |- .+ = ( +g ` G )

  disjoint B l
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint l r
  disjoint l x
  disjoint l y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint G l
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint .+ l
  disjoint .+ r
  disjoint .+ x
  disjoint .+ y
  disjoint B a
  disjoint B i
  disjoint B u
  disjoint B w
  disjoint B z
  disjoint a i
  disjoint a l
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint i l
  disjoint i r
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint l u
  disjoint l w
  disjoint l z
  disjoint r u
  disjoint r w
  disjoint r z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint G a
  disjoint G i
  disjoint G u
  disjoint G w
  disjoint G z
  disjoint .+ a
  disjoint .+ i
  disjoint .+ u
  disjoint .+ w
  disjoint .+ z
  assert |- ( G e. Grp <-> ( G e. SGrp /\ B =/= (/) /\ A. x e. B A. y e. B ( E. l e. B ( l .+ x ) = y /\ E. r e. B ( x .+ r ) = y ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    csgrp
    wcel
    #
    cB
    c0
    wne
    #
    vl
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    vy
    cv
    #
    wceq
    #
    vl
    cB
    wrex
    #
    @4
    vr
    cv
    #
    c.pl
    co
    #
    @6
    wceq
    #
    vr
    cB
    wrex
    #
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    w3a
    #
    @0
    @1
    @2
    @14
    cG
    grpsgrp
    cB
    cG
    dfgrp3.b
    grpbn0
    @0
    @13
    vx
    vy
    cB
    cB
    @0
    @4
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    @8
    @12
    @19
    @7
    @6
    @4
    cG
    csg
    cfv
    #
    co
    #
    @4
    c.pl
    co
    #
    @6
    wceq
    #
    vl
    @21
    cB
    @19
    @0
    @17
    @16
    @21
    cB
    wcel
    @0
    @18
    simpl
    #
    @18
    @17
    @0
    @16
    @17
    simpr
    #
    adantl
    #
    @18
    @16
    @0
    @16
    @17
    simpl
    adantl
    #
    cB
    cG
    @20
    @6
    @4
    dfgrp3.b
    @20
    eqid
    #
    grpsubcl
    syl3anc
    @3
    @21
    wceq
    #
    @7
    @23
    wb
    @19
    @29
    @5
    @22
    @6
    @3
    @21
    @4
    c.pl
    oveq1
    eqeq1d
    adantl
    @19
    @0
    @17
    @16
    @23
    @24
    @26
    @27
    cB
    c.pl
    cG
    @20
    @6
    @4
    dfgrp3.b
    dfgrp3.p
    @28
    grpnpcan
    syl3anc
    rspcedvd
    @19
    @11
    @4
    @4
    cG
    cminusg
    cfv
    #
    cfv
    #
    @6
    c.pl
    co
    #
    c.pl
    co
    #
    @6
    wceq
    #
    vr
    @32
    cB
    @19
    @0
    @31
    cB
    wcel
    #
    @17
    @32
    cB
    wcel
    @24
    @0
    @16
    @35
    @17
    cB
    cG
    @30
    @4
    dfgrp3.b
    @30
    eqid
    #
    grpinvcl
    adantrr
    #
    @26
    cB
    c.pl
    cG
    @31
    @6
    dfgrp3.b
    dfgrp3.p
    grpcl
    syl3anc
    @9
    @32
    wceq
    #
    @11
    @34
    wb
    @19
    @38
    @10
    @33
    @6
    @9
    @32
    @4
    c.pl
    oveq2
    eqeq1d
    adantl
    @19
    @4
    @31
    c.pl
    co
    #
    @6
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @6
    c.pl
    co
    #
    @33
    @6
    @19
    @39
    @41
    @6
    c.pl
    @0
    @16
    @39
    @41
    wceq
    @17
    cB
    c.pl
    cG
    @30
    @4
    @41
    dfgrp3.b
    dfgrp3.p
    @41
    eqid
    #
    @36
    grprinv
    adantrr
    oveq1d
    @19
    @0
    @16
    @35
    @17
    @40
    @33
    wceq
    @24
    @27
    @37
    @26
    cB
    c.pl
    cG
    @4
    @31
    @6
    dfgrp3.b
    dfgrp3.p
    grpass
    syl13anc
    @0
    cG
    cmnd
    wcel
    @17
    @42
    @6
    wceq
    @18
    cG
    grpmnd
    @25
    cB
    c.pl
    cG
    @6
    @41
    dfgrp3.b
    dfgrp3.p
    @43
    mndlid
    syl2an
    3eqtr3d
    rspcedvd
    jca
    ralrimivva
    3jca
    @15
    @1
    vu
    cv
    #
    va
    cv
    #
    c.pl
    co
    @45
    wceq
    vi
    cv
    @45
    c.pl
    co
    @44
    wceq
    vi
    cB
    wrex
    wa
    va
    cB
    wral
    vu
    cB
    wrex
    @0
    @1
    @2
    @14
    simp1
    vx
    vy
    vu
    cB
    c.pl
    vi
    cG
    vr
    va
    vl
    dfgrp3.b
    dfgrp3.p
    dfgrp3lem
    va
    cB
    c.pl
    vi
    vu
    cG
    dfgrp3.b
    dfgrp3.p
    dfgrp2
    sylanbrc
    impbii
end
