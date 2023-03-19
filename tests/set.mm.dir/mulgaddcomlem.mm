include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cz.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cneg.mm"
include "cminusg.mm"
include "cfv.mm"
include "simp1.mm"
include "adantr.mm"
include "simp3.mm"
include "znegcl.mm"
include "mulgcl.mm"
include "syl3an2.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "grpass.mm"
include "syl13anc.mm"
include "mulgneg.mm"
include "oveq1d.mm"
include "grpinvadd.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "adantl.mm"
include "3eqtr2rd.mm"
include "3eqtr2d.mm"
include "grpasscan1.mm"
include "3eqtrd.mm"
include "grpcl.mm"
include "grpasscan2.mm"
include "eqtr3d.mm"

theorem mulgaddcomlem
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cX: class X
  assume mulgaddcom.b: |- B = ( Base ` G )
  assume mulgaddcom.t: |- .x. = ( .g ` G )
  assume mulgaddcom.p: |- .+ = ( +g ` G )


  assert |- ( ( ( G e. Grp /\ y e. ZZ /\ X e. B ) /\ ( ( y .x. X ) .+ X ) = ( X .+ ( y .x. X ) ) ) -> ( ( -u y .x. X ) .+ X ) = ( X .+ ( -u y .x. X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    vy
    cv
    #
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    @1
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    @5
    c.pl
    co
    #
    wceq
    #
    wa
    #
    cX
    @1
    cneg
    #
    cX
    c.x
    co
    #
    c.pl
    co
    #
    cX
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cX
    c.pl
    co
    #
    @11
    cX
    c.pl
    co
    @12
    @9
    @15
    @11
    cX
    c.pl
    @9
    @15
    cX
    @11
    @14
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    @14
    @11
    c.pl
    co
    #
    c.pl
    co
    #
    @11
    @9
    @0
    @3
    @11
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    @15
    @18
    wceq
    @4
    @0
    @8
    @0
    @2
    @3
    simp1
    #
    adantr
    #
    @4
    @3
    @8
    @0
    @2
    @3
    simp3
    #
    adantr
    #
    @4
    @21
    @8
    @2
    @0
    @10
    cz
    wcel
    @3
    @21
    @1
    znegcl
    cB
    c.x
    cG
    @10
    cX
    mulgaddcom.b
    mulgaddcom.t
    mulgcl
    syl3an2
    #
    adantr
    #
    @4
    @22
    @8
    @0
    @3
    @22
    @2
    cB
    cG
    @13
    cX
    mulgaddcom.b
    @13
    eqid
    #
    grpinvcl
    3adant2
    adantr
    cB
    c.pl
    cG
    cX
    @11
    @14
    mulgaddcom.b
    mulgaddcom.p
    grpass
    syl13anc
    @9
    @17
    @19
    cX
    c.pl
    @9
    @17
    @5
    @13
    cfv
    #
    @14
    c.pl
    co
    #
    @7
    @13
    cfv
    #
    @19
    @9
    @11
    @30
    @14
    c.pl
    @4
    @11
    @30
    wceq
    @8
    cB
    c.x
    cG
    @13
    @1
    cX
    mulgaddcom.b
    mulgaddcom.t
    @29
    mulgneg
    adantr
    #
    oveq1d
    @9
    @0
    @3
    @5
    cB
    wcel
    #
    @32
    @31
    wceq
    @24
    @26
    @4
    @34
    @8
    cB
    c.x
    cG
    @1
    cX
    mulgaddcom.b
    mulgaddcom.t
    mulgcl
    adantr
    #
    cB
    c.pl
    cG
    @13
    cX
    @5
    mulgaddcom.b
    mulgaddcom.p
    @29
    grpinvadd
    syl3anc
    @9
    @19
    @14
    @30
    c.pl
    co
    #
    @6
    @13
    cfv
    #
    @32
    @9
    @11
    @30
    @14
    c.pl
    @33
    oveq2d
    @9
    @0
    @34
    @3
    @37
    @36
    wceq
    @24
    @35
    @26
    cB
    c.pl
    cG
    @13
    @5
    cX
    mulgaddcom.b
    mulgaddcom.p
    @29
    grpinvadd
    syl3anc
    @8
    @37
    @32
    wceq
    @4
    @6
    @7
    @13
    fveq2
    adantl
    3eqtr2rd
    3eqtr2d
    oveq2d
    @9
    @0
    @3
    @21
    @20
    @11
    wceq
    @24
    @26
    @28
    cB
    c.pl
    cG
    @13
    cX
    @11
    mulgaddcom.b
    mulgaddcom.p
    @29
    grpasscan1
    syl3anc
    3eqtrd
    oveq1d
    @9
    @0
    @12
    cB
    wcel
    #
    @3
    @16
    @12
    wceq
    @24
    @4
    @38
    @8
    @4
    @0
    @3
    @21
    @38
    @23
    @25
    @27
    cB
    c.pl
    cG
    cX
    @11
    mulgaddcom.b
    mulgaddcom.p
    grpcl
    syl3anc
    adantr
    @26
    cB
    c.pl
    cG
    @13
    @12
    cX
    mulgaddcom.b
    mulgaddcom.p
    @29
    grpasscan2
    syl3anc
    eqtr3d
end
