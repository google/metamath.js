include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "wceq.mm"
include "cneg.mm"
include "mulgdirlem.mm"
include "3expa.mm"
include "cminusg.mm"
include "cfv.mm"
include "simpll.mm"
include "simpr2.mm"
include "adantr.mm"
include "znegcld.mm"
include "simpr1.mm"
include "simplr3.mm"
include "zcnd.mm"
include "negdid.mm"
include "negcld.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "syl131anc.mm"
include "oveq1d.mm"
include "zaddcld.mm"
include "eqid.mm"
include "mulgneg.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "mulgcl.mm"
include "grpinvadd.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "grpinvinv.mm"
include "syl2anc.mm"
include "grpcl.mm"
include "wo.mm"
include "cr.mm"
include "elznn0.mm"
include "simprbi.mm"
include "syl.mm"
include "mpjaodan.mm"

theorem mulgdir
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mulgnndir.b: |- B = ( Base ` G )
  assume mulgnndir.t: |- .x. = ( .g ` G )
  assume mulgnndir.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ ( M e. ZZ /\ N e. ZZ /\ X e. B ) ) -> ( ( M + N ) .x. X ) = ( ( M .x. X ) .+ ( N .x. X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cM
    cN
    caddc
    co
    #
    cn0
    wcel
    #
    @6
    cX
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @6
    cneg
    #
    cn0
    wcel
    #
    @0
    @4
    @7
    @12
    cB
    c.pl
    c.x
    cG
    cM
    cN
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnndir.p
    mulgdirlem
    3expa
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
    @16
    cfv
    #
    @11
    @16
    cfv
    #
    @16
    cfv
    #
    @8
    @11
    @15
    @17
    @19
    @16
    @15
    cN
    cneg
    #
    cM
    cneg
    #
    caddc
    co
    #
    cX
    c.x
    co
    #
    @21
    cX
    c.x
    co
    #
    @22
    cX
    c.x
    co
    #
    c.pl
    co
    #
    @17
    @19
    @15
    @0
    @21
    cz
    wcel
    @22
    cz
    wcel
    @3
    @23
    cn0
    wcel
    @24
    @27
    wceq
    @0
    @4
    @14
    simpll
    #
    @15
    cN
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
    #
    znegcld
    @15
    cM
    @5
    @1
    @14
    @0
    @1
    @2
    @3
    simpr1
    #
    adantr
    #
    znegcld
    @1
    @2
    @3
    @0
    @14
    simplr3
    #
    @15
    @13
    @23
    cn0
    @15
    @13
    @22
    @21
    caddc
    co
    @23
    @15
    cM
    cN
    @15
    cM
    @32
    zcnd
    #
    @15
    cN
    @30
    zcnd
    #
    negdid
    @15
    @22
    @21
    @15
    cM
    @34
    negcld
    @15
    cN
    @35
    negcld
    addcomd
    eqtrd
    #
    @5
    @14
    simpr
    eqeltrrd
    cB
    c.pl
    c.x
    cG
    @21
    @22
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnndir.p
    mulgdirlem
    syl131anc
    @15
    @13
    cX
    c.x
    co
    #
    @24
    @17
    @15
    @13
    @23
    cX
    c.x
    @36
    oveq1d
    @15
    @0
    @6
    cz
    wcel
    #
    @3
    @37
    @17
    wceq
    @28
    @5
    @38
    @14
    @5
    cM
    cN
    @31
    @29
    zaddcld
    #
    adantr
    #
    @33
    cB
    c.x
    cG
    @16
    @6
    cX
    mulgnndir.b
    mulgnndir.t
    @16
    eqid
    #
    mulgneg
    syl3anc
    eqtr3d
    @15
    @27
    @10
    @16
    cfv
    #
    @9
    @16
    cfv
    #
    c.pl
    co
    #
    @19
    @15
    @25
    @42
    @26
    @43
    c.pl
    @15
    @0
    @2
    @3
    @25
    @42
    wceq
    @28
    @30
    @33
    cB
    c.x
    cG
    @16
    cN
    cX
    mulgnndir.b
    mulgnndir.t
    @41
    mulgneg
    syl3anc
    @15
    @0
    @1
    @3
    @26
    @43
    wceq
    @28
    @32
    @33
    cB
    c.x
    cG
    @16
    cM
    cX
    mulgnndir.b
    mulgnndir.t
    @41
    mulgneg
    syl3anc
    oveq12d
    @15
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @19
    @44
    wceq
    @28
    @15
    @0
    @1
    @3
    @45
    @28
    @32
    @33
    cB
    c.x
    cG
    cM
    cX
    mulgnndir.b
    mulgnndir.t
    mulgcl
    syl3anc
    #
    @15
    @0
    @2
    @3
    @46
    @28
    @30
    @33
    cB
    c.x
    cG
    cN
    cX
    mulgnndir.b
    mulgnndir.t
    mulgcl
    syl3anc
    #
    cB
    c.pl
    cG
    @16
    @9
    @10
    mulgnndir.b
    mulgnndir.p
    @41
    grpinvadd
    syl3anc
    eqtr4d
    3eqtr3d
    fveq2d
    @15
    @0
    @8
    cB
    wcel
    #
    @18
    @8
    wceq
    @28
    @15
    @0
    @38
    @3
    @49
    @28
    @40
    @33
    cB
    c.x
    cG
    @6
    cX
    mulgnndir.b
    mulgnndir.t
    mulgcl
    syl3anc
    cB
    cG
    @16
    @8
    mulgnndir.b
    @41
    grpinvinv
    syl2anc
    @15
    @0
    @11
    cB
    wcel
    #
    @20
    @11
    wceq
    @28
    @15
    @0
    @45
    @46
    @50
    @28
    @47
    @48
    cB
    c.pl
    cG
    @9
    @10
    mulgnndir.b
    mulgnndir.p
    grpcl
    syl3anc
    cB
    cG
    @16
    @11
    mulgnndir.b
    @41
    grpinvinv
    syl2anc
    3eqtr3d
    @5
    @38
    @7
    @14
    wo
    #
    @39
    @38
    @6
    cr
    wcel
    @51
    @6
    elznn0
    simprbi
    syl
    mpjaodan
end
