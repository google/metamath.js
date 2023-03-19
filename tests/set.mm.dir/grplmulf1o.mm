include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "grpcl.mm"
include "3expa.mm"
include "simpl.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "jca.mm"
include "sylan.mm"
include "wceq.mm"
include "eqcom.mm"
include "wb.mm"
include "adantr.mm"
include "adantrl.mm"
include "simprl.mm"
include "simplr.mm"
include "grplcan.mm"
include "syl13anc.mm"
include "c0g.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "simprr.mm"
include "grpass.mm"
include "grplid.mm"
include "ad2ant2rl.mm"
include "3eqtr3d.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "f1o2d.mm"

theorem grplmulf1o
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cX: class X
  let vy: setvar y
  assume grplmulf1o.b: |- B = ( Base ` G )
  assume grplmulf1o.p: |- .+ = ( +g ` G )
  assume grplmulf1o.n: |- F = ( x e. B |-> ( X .+ x ) )

  disjoint B x
  disjoint G x
  disjoint .+ x
  disjoint X x
  disjoint x y
  disjoint B y
  disjoint G y
  disjoint .+ y
  disjoint X y
  assert |- ( ( G e. Grp /\ X e. B ) -> F : B -1-1-onto-> B )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vx
    vy
    cB
    cB
    cX
    vx
    cv
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
    vy
    cv
    #
    c.pl
    co
    #
    cF
    grplmulf1o.n
    @0
    @1
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    cB
    c.pl
    cG
    cX
    @3
    grplmulf1o.b
    grplmulf1o.p
    grpcl
    3expa
    @2
    @0
    @6
    cB
    wcel
    #
    wa
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @2
    @0
    @10
    @0
    @1
    simpl
    #
    cB
    cG
    @5
    cX
    grplmulf1o.b
    @5
    eqid
    #
    grpinvcl
    #
    jca
    @0
    @10
    @11
    @12
    cB
    c.pl
    cG
    @6
    @7
    grplmulf1o.b
    grplmulf1o.p
    grpcl
    3expa
    sylan
    #
    @3
    @8
    wceq
    @8
    @3
    wceq
    #
    @2
    @9
    @11
    wa
    #
    wa
    #
    @7
    @4
    wceq
    #
    @3
    @8
    eqcom
    @19
    cX
    @8
    c.pl
    co
    #
    @4
    wceq
    #
    @17
    @20
    @19
    @0
    @12
    @9
    @1
    @22
    @17
    wb
    @2
    @0
    @18
    @13
    adantr
    #
    @2
    @11
    @12
    @9
    @16
    adantrl
    @2
    @9
    @11
    simprl
    @0
    @1
    @18
    simplr
    #
    cB
    c.pl
    cG
    @8
    @3
    cX
    grplmulf1o.b
    grplmulf1o.p
    grplcan
    syl13anc
    @19
    @21
    @7
    @4
    @19
    cX
    @6
    c.pl
    co
    #
    @7
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @7
    c.pl
    co
    #
    @21
    @7
    @19
    @25
    @27
    @7
    c.pl
    @2
    @25
    @27
    wceq
    @18
    cB
    c.pl
    cG
    @5
    cX
    @27
    grplmulf1o.b
    grplmulf1o.p
    @27
    eqid
    #
    @14
    grprinv
    adantr
    oveq1d
    @19
    @0
    @1
    @10
    @11
    @26
    @21
    wceq
    @23
    @24
    @2
    @10
    @18
    @15
    adantr
    @2
    @9
    @11
    simprr
    cB
    c.pl
    cG
    cX
    @6
    @7
    grplmulf1o.b
    grplmulf1o.p
    grpass
    syl13anc
    @0
    @11
    @28
    @7
    wceq
    @1
    @9
    cB
    c.pl
    cG
    @7
    @27
    grplmulf1o.b
    grplmulf1o.p
    @29
    grplid
    ad2ant2rl
    3eqtr3d
    eqeq1d
    bitr3d
    syl5bb
    f1o2d
end
