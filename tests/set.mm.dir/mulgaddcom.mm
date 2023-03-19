include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "grplid.mm"
include "mulg0.mm"
include "adantl.mm"
include "grprid.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "cn0.mm"
include "w3a.mm"
include "nn0z.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3jca.mm"
include "mulgcl.mm"
include "syl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "syl3an3.mm"
include "adantr.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "3ad2ant1.mm"
include "mulgnn0p1.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "ex.mm"
include "3expia.mm"
include "cn.mm"
include "nnz.mm"
include "mulgaddcomlem.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "syl5.mm"
include "zindd.mm"
include "3imp.mm"

theorem mulgaddcom
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulgaddcom.b: |- B = ( Base ` G )
  assume mulgaddcom.t: |- .x. = ( .g ` G )
  assume mulgaddcom.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( ( N .x. X ) .+ X ) = ( X .+ ( N .x. X ) ) )

  proof
    cG
    cgrp
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
    cN
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @3
    c.pl
    co
    #
    wceq
    #
    @0
    @2
    @1
    @6
    @0
    @2
    @1
    @6
    wi
    vx
    cv
    #
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @8
    c.pl
    co
    #
    wceq
    cc0
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @11
    c.pl
    co
    #
    wceq
    vy
    cv
    #
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @15
    c.pl
    co
    #
    wceq
    #
    @14
    cneg
    #
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @20
    c.pl
    co
    #
    wceq
    #
    @14
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @25
    c.pl
    co
    #
    wceq
    #
    @6
    @0
    @2
    wa
    #
    vx
    vy
    cN
    @7
    cc0
    wceq
    #
    @9
    @12
    @10
    @13
    @30
    @8
    @11
    cX
    c.pl
    @7
    cc0
    cX
    c.x
    oveq1
    #
    oveq1d
    @30
    @8
    @11
    cX
    c.pl
    @31
    oveq2d
    eqeq12d
    vx
    vy
    weq
    #
    @9
    @16
    @10
    @17
    @32
    @8
    @15
    cX
    c.pl
    @7
    @14
    cX
    c.x
    oveq1
    #
    oveq1d
    @32
    @8
    @15
    cX
    c.pl
    @33
    oveq2d
    eqeq12d
    @7
    @24
    wceq
    #
    @9
    @26
    @10
    @27
    @34
    @8
    @25
    cX
    c.pl
    @7
    @24
    cX
    c.x
    oveq1
    #
    oveq1d
    @34
    @8
    @25
    cX
    c.pl
    @35
    oveq2d
    eqeq12d
    @7
    @19
    wceq
    #
    @9
    @21
    @10
    @22
    @36
    @8
    @20
    cX
    c.pl
    @7
    @19
    cX
    c.x
    oveq1
    #
    oveq1d
    @36
    @8
    @20
    cX
    c.pl
    @37
    oveq2d
    eqeq12d
    @7
    cN
    wceq
    #
    @9
    @4
    @10
    @5
    @38
    @8
    @3
    cX
    c.pl
    @7
    cN
    cX
    c.x
    oveq1
    #
    oveq1d
    @38
    @8
    @3
    cX
    c.pl
    @39
    oveq2d
    eqeq12d
    @29
    cG
    c0g
    cfv
    #
    cX
    c.pl
    co
    cX
    @12
    @13
    cB
    c.pl
    cG
    cX
    @40
    mulgaddcom.b
    mulgaddcom.p
    @40
    eqid
    #
    grplid
    @29
    @11
    @40
    cX
    c.pl
    @2
    @11
    @40
    wceq
    @0
    cB
    c.x
    cG
    cX
    @40
    mulgaddcom.b
    @41
    mulgaddcom.t
    mulg0
    adantl
    #
    oveq1d
    @29
    @13
    cX
    @40
    c.pl
    co
    cX
    @29
    @11
    @40
    cX
    c.pl
    @42
    oveq2d
    cB
    c.pl
    cG
    cX
    @40
    mulgaddcom.b
    mulgaddcom.p
    @41
    grprid
    eqtrd
    3eqtr4d
    @0
    @2
    @14
    cn0
    wcel
    #
    @18
    @28
    wi
    @0
    @2
    @43
    w3a
    #
    @18
    @28
    @44
    @18
    wa
    #
    @17
    cX
    c.pl
    co
    #
    cX
    @16
    c.pl
    co
    #
    @26
    @27
    @44
    @46
    @47
    wceq
    #
    @18
    @43
    @0
    @2
    @14
    cz
    wcel
    #
    @48
    @14
    nn0z
    @0
    @2
    @49
    w3a
    #
    @0
    @2
    @15
    cB
    wcel
    #
    @2
    @48
    @0
    @2
    @49
    simp1
    #
    @0
    @2
    @49
    simp2
    #
    @50
    @0
    @49
    @2
    w3a
    #
    @51
    @50
    @0
    @49
    @2
    @52
    @0
    @2
    @49
    simp3
    @53
    3jca
    cB
    c.x
    cG
    @14
    cX
    mulgaddcom.b
    mulgaddcom.t
    mulgcl
    syl
    @53
    cB
    c.pl
    cG
    cX
    @15
    cX
    mulgaddcom.b
    mulgaddcom.p
    grpass
    syl13anc
    syl3an3
    adantr
    @45
    @25
    @17
    cX
    c.pl
    @44
    @25
    @17
    wceq
    @18
    @44
    @25
    @16
    @17
    @44
    cG
    cmnd
    wcel
    #
    @43
    @2
    w3a
    @25
    @16
    wceq
    @44
    @55
    @43
    @2
    @0
    @2
    @55
    @43
    cG
    grpmnd
    3ad2ant1
    @0
    @2
    @43
    simp3
    @0
    @2
    @43
    simp2
    3jca
    cB
    c.pl
    c.x
    cG
    @14
    cX
    mulgaddcom.b
    mulgaddcom.t
    mulgaddcom.p
    mulgnn0p1
    syl
    #
    eqeq1d
    biimpar
    oveq1d
    @44
    @27
    @47
    wceq
    @18
    @44
    @25
    @16
    cX
    c.pl
    @56
    oveq2d
    adantr
    3eqtr4d
    ex
    3expia
    @14
    cn
    wcel
    @49
    @29
    @18
    @23
    wi
    #
    @14
    nnz
    @0
    @2
    @49
    @57
    wi
    @0
    @49
    @2
    @57
    @0
    @49
    @2
    @57
    @54
    @18
    @23
    vy
    cB
    c.pl
    c.x
    cG
    cX
    mulgaddcom.b
    mulgaddcom.t
    mulgaddcom.p
    mulgaddcomlem
    ex
    3exp
    com23
    imp
    syl5
    zindd
    ex
    com23
    3imp
end
