include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "znegcl.mm"
include "eqid.mm"
include "mulgdir.mm"
include "syl3anr2.mm"
include "simpr1.mm"
include "zcnd.mm"
include "simpr2.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "cminusg.mm"
include "mulgneg.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "mulgcl.mm"
include "3adant3r2.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"

theorem mulgsubdir
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume mulgsubdir.b: |- B = ( Base ` G )
  assume mulgsubdir.t: |- .x. = ( .g ` G )
  assume mulgsubdir.d: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( M e. ZZ /\ N e. ZZ /\ X e. B ) ) -> ( ( M - N ) .x. X ) = ( ( M .x. X ) .- ( N .x. X ) ) )

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
    wa
    #
    cM
    cN
    cneg
    #
    caddc
    co
    #
    cX
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    @5
    cX
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cM
    cN
    cmin
    co
    #
    cX
    c.x
    co
    @8
    cN
    cX
    c.x
    co
    #
    c.mi
    co
    #
    @2
    @1
    @0
    @5
    cz
    wcel
    @3
    @7
    @11
    wceq
    cN
    znegcl
    cB
    @10
    c.x
    cG
    cM
    @5
    cX
    mulgsubdir.b
    mulgsubdir.t
    @10
    eqid
    #
    mulgdir
    syl3anr2
    @4
    @6
    @12
    cX
    c.x
    @4
    cM
    cN
    @4
    cM
    @0
    @1
    @2
    @3
    simpr1
    zcnd
    @4
    cN
    @0
    @1
    @2
    @3
    simpr2
    zcnd
    negsubd
    oveq1d
    @4
    @11
    @8
    @13
    cG
    cminusg
    cfv
    #
    cfv
    #
    @10
    co
    #
    @14
    @4
    @9
    @17
    @8
    @10
    @0
    @2
    @3
    @9
    @17
    wceq
    @1
    cB
    c.x
    cG
    @16
    cN
    cX
    mulgsubdir.b
    mulgsubdir.t
    @16
    eqid
    #
    mulgneg
    3adant3r1
    oveq2d
    @4
    @8
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @14
    @18
    wceq
    @0
    @1
    @3
    @20
    @2
    cB
    c.x
    cG
    cM
    cX
    mulgsubdir.b
    mulgsubdir.t
    mulgcl
    3adant3r2
    @0
    @2
    @3
    @21
    @1
    cB
    c.x
    cG
    cN
    cX
    mulgsubdir.b
    mulgsubdir.t
    mulgcl
    3adant3r1
    cB
    @10
    cG
    @16
    c.mi
    @8
    @13
    mulgsubdir.b
    @15
    @19
    mulgsubdir.d
    grpsubval
    syl2anc
    eqtr4d
    3eqtr3d
end
