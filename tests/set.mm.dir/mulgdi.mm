include "cabl.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cn0.mm"
include "co.mm"
include "wceq.mm"
include "cneg.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr2.mm"
include "simplr3.mm"
include "mulgnn0di.mm"
include "syl13anc.mm"
include "cminusg.mm"
include "cfv.mm"
include "simpr2.mm"
include "adantr.mm"
include "simpr3.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "simpr1.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "mulgneg.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "simpl.mm"
include "mulgcl.mm"
include "ablinvadd.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "grpinvinv.mm"
include "syl2anc.mm"
include "wo.mm"
include "cr.mm"
include "elznn0.mm"
include "simprbi.mm"
include "syl.mm"
include "mpjaodan.mm"

theorem mulgdi
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mulgdi.b: |- B = ( Base ` G )
  assume mulgdi.m: |- .x. = ( .g ` G )
  assume mulgdi.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Abel /\ ( M e. ZZ /\ X e. B /\ Y e. B ) ) -> ( M .x. ( X .+ Y ) ) = ( ( M .x. X ) .+ ( M .x. Y ) ) )

  proof
    cG
    cabl
    wcel
    #
    cM
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cM
    cn0
    wcel
    #
    cM
    cX
    cY
    c.pl
    co
    #
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cM
    cY
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    cM
    cneg
    #
    cn0
    wcel
    #
    @5
    @6
    wa
    cG
    ccmn
    wcel
    #
    @6
    @2
    @3
    @12
    @0
    @15
    @4
    @6
    cG
    ablcmn
    #
    ad2antrr
    @5
    @6
    simpr
    @1
    @2
    @3
    @0
    @6
    simplr2
    @1
    @2
    @3
    @0
    @6
    simplr3
    cB
    c.pl
    c.x
    cG
    cM
    cX
    cY
    mulgdi.b
    mulgdi.m
    mulgdi.p
    mulgnn0di
    syl13anc
    @5
    @14
    wa
    #
    @8
    cG
    cminusg
    cfv
    #
    cfv
    #
    @18
    cfv
    #
    @11
    @18
    cfv
    #
    @18
    cfv
    #
    @8
    @11
    @17
    @19
    @21
    @18
    @17
    @19
    @9
    @18
    cfv
    #
    @10
    @18
    cfv
    #
    c.pl
    co
    #
    @21
    @17
    @13
    @7
    c.x
    co
    #
    @13
    cX
    c.x
    co
    #
    @13
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @19
    @25
    @17
    @15
    @14
    @2
    @3
    @26
    @29
    wceq
    @0
    @15
    @4
    @14
    @16
    ad2antrr
    @5
    @14
    simpr
    @5
    @2
    @14
    @0
    @1
    @2
    @3
    simpr2
    #
    adantr
    @5
    @3
    @14
    @0
    @1
    @2
    @3
    simpr3
    #
    adantr
    cB
    c.pl
    c.x
    cG
    @13
    cX
    cY
    mulgdi.b
    mulgdi.m
    mulgdi.p
    mulgnn0di
    syl13anc
    @5
    @26
    @19
    wceq
    #
    @14
    @5
    cG
    cgrp
    wcel
    #
    @1
    @7
    cB
    wcel
    #
    @32
    @0
    @33
    @4
    cG
    ablgrp
    #
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @5
    @33
    @2
    @3
    @34
    @36
    @30
    @31
    cB
    c.pl
    cG
    cX
    cY
    mulgdi.b
    mulgdi.p
    grpcl
    syl3anc
    #
    cB
    c.x
    cG
    @18
    cM
    @7
    mulgdi.b
    mulgdi.m
    @18
    eqid
    #
    mulgneg
    syl3anc
    adantr
    @5
    @29
    @25
    wceq
    @14
    @5
    @27
    @23
    @28
    @24
    c.pl
    @5
    @33
    @1
    @2
    @27
    @23
    wceq
    @36
    @37
    @30
    cB
    c.x
    cG
    @18
    cM
    cX
    mulgdi.b
    mulgdi.m
    @39
    mulgneg
    syl3anc
    @5
    @33
    @1
    @3
    @28
    @24
    wceq
    @36
    @37
    @31
    cB
    c.x
    cG
    @18
    cM
    cY
    mulgdi.b
    mulgdi.m
    @39
    mulgneg
    syl3anc
    oveq12d
    adantr
    3eqtr3d
    @5
    @21
    @25
    wceq
    #
    @14
    @5
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @40
    @0
    @4
    simpl
    @5
    @33
    @1
    @2
    @41
    @36
    @37
    @30
    cB
    c.x
    cG
    cM
    cX
    mulgdi.b
    mulgdi.m
    mulgcl
    syl3anc
    #
    @5
    @33
    @1
    @3
    @42
    @36
    @37
    @31
    cB
    c.x
    cG
    cM
    cY
    mulgdi.b
    mulgdi.m
    mulgcl
    syl3anc
    #
    cB
    c.pl
    cG
    @18
    @9
    @10
    mulgdi.b
    mulgdi.p
    @39
    ablinvadd
    syl3anc
    adantr
    eqtr4d
    fveq2d
    @17
    @33
    @8
    cB
    wcel
    #
    @20
    @8
    wceq
    @0
    @33
    @4
    @14
    @35
    ad2antrr
    #
    @5
    @45
    @14
    @5
    @33
    @1
    @34
    @45
    @36
    @37
    @38
    cB
    c.x
    cG
    cM
    @7
    mulgdi.b
    mulgdi.m
    mulgcl
    syl3anc
    adantr
    cB
    cG
    @18
    @8
    mulgdi.b
    @39
    grpinvinv
    syl2anc
    @17
    @33
    @11
    cB
    wcel
    #
    @22
    @11
    wceq
    @46
    @5
    @47
    @14
    @5
    @33
    @41
    @42
    @47
    @36
    @43
    @44
    cB
    c.pl
    cG
    @9
    @10
    mulgdi.b
    mulgdi.p
    grpcl
    syl3anc
    adantr
    cB
    cG
    @18
    @11
    mulgdi.b
    @39
    grpinvinv
    syl2anc
    3eqtr3d
    @5
    @1
    @6
    @14
    wo
    #
    @37
    @1
    cM
    cr
    wcel
    @48
    cM
    elznn0
    simprbi
    syl
    mpjaodan
end
