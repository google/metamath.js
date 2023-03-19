include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "wceq.mm"
include "unitss.mm"
include "simpr3.mm"
include "sseldi.mm"
include "unitmulcl.mm"
include "3adant3r1.mm"
include "eqid.mm"
include "dvrval.mm"
include "syl2anc.mm"
include "cmgp.mm"
include "cress.mm"
include "cgrp.mm"
include "simpl.mm"
include "unitgrp.mm"
include "syl.mm"
include "simpr2.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "invrfval.mm"
include "grpinvadd.mm"
include "oveq2d.mm"
include "syl3anc.mm"
include "cur.mm"
include "unitrinv.mm"
include "oveq1d.mm"
include "3ad2antr3.mm"
include "unitinvcl.mm"
include "3ad2antr2.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "simpr1.mm"
include "dvrass.mm"
include "3eqtr4d.mm"

theorem dvrcan5
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvrcan5.b: |- B = ( Base ` R )
  assume dvrcan5.o: |- U = ( Unit ` R )
  assume dvrcan5.d: |- ./ = ( /r ` R )
  assume dvrcan5.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. U /\ Z e. U ) ) -> ( ( X .x. Z ) ./ ( Y .x. Z ) ) = ( X ./ Y ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    cZ
    cU
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cZ
    cY
    cZ
    c.x
    co
    #
    c.dv
    co
    #
    c.x
    co
    #
    cX
    cY
    cR
    cinvr
    cfv
    #
    cfv
    #
    c.x
    co
    #
    cX
    cZ
    c.x
    co
    @6
    c.dv
    co
    #
    cX
    cY
    c.dv
    co
    #
    @5
    @7
    @10
    cX
    c.x
    @5
    @7
    cZ
    @6
    @9
    cfv
    #
    c.x
    co
    #
    cZ
    cZ
    @9
    cfv
    #
    @10
    c.x
    co
    #
    c.x
    co
    #
    @10
    @5
    cZ
    cB
    wcel
    #
    @6
    cU
    wcel
    #
    @7
    @15
    wceq
    @5
    cU
    cB
    cZ
    cB
    cR
    cU
    dvrcan5.b
    dvrcan5.o
    unitss
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    sseldi
    #
    @0
    @2
    @3
    @20
    @1
    cR
    c.x
    cU
    cY
    cZ
    dvrcan5.o
    dvrcan5.t
    unitmulcl
    3adant3r1
    #
    cB
    c.dv
    cR
    c.x
    cU
    @9
    cZ
    @6
    dvrcan5.b
    dvrcan5.t
    dvrcan5.o
    @9
    eqid
    #
    dvrcan5.d
    dvrval
    syl2anc
    @5
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    cgrp
    wcel
    #
    @2
    @3
    @15
    @18
    wceq
    @5
    @0
    @28
    @0
    @4
    simpl
    #
    cR
    cU
    @27
    dvrcan5.o
    @27
    eqid
    #
    unitgrp
    syl
    @0
    @1
    @2
    @3
    simpr2
    #
    @22
    @28
    @2
    @3
    w3a
    @14
    @17
    cZ
    c.x
    cU
    c.x
    @27
    @9
    cY
    cZ
    cR
    cU
    @27
    dvrcan5.o
    @30
    unitgrpbas
    cU
    cvv
    wcel
    c.x
    @27
    cplusg
    cfv
    wceq
    cU
    cR
    cui
    cfv
    cvv
    dvrcan5.o
    cR
    cui
    fvex
    eqeltri
    cU
    c.x
    @26
    @27
    cvv
    @30
    cR
    c.x
    @26
    @26
    eqid
    dvrcan5.t
    mgpplusg
    ressplusg
    ax-mp
    cR
    cU
    @27
    @9
    dvrcan5.o
    @30
    @25
    invrfval
    grpinvadd
    oveq2d
    syl3anc
    @5
    cZ
    @16
    c.x
    co
    #
    @10
    c.x
    co
    #
    cR
    cur
    cfv
    #
    @10
    c.x
    co
    #
    @18
    @10
    @0
    @1
    @3
    @33
    @35
    wceq
    @2
    @0
    @3
    wa
    @32
    @34
    @10
    c.x
    cR
    c.x
    cU
    @34
    @9
    cZ
    dvrcan5.o
    @25
    dvrcan5.t
    @34
    eqid
    #
    unitrinv
    oveq1d
    3ad2antr3
    @5
    @0
    @19
    @16
    cB
    wcel
    @10
    cB
    wcel
    #
    @33
    @18
    wceq
    @29
    @23
    @5
    cU
    cB
    @16
    @21
    @0
    @1
    @3
    @16
    cU
    wcel
    @2
    cR
    cU
    @9
    cZ
    dvrcan5.o
    @25
    unitinvcl
    3ad2antr3
    sseldi
    @5
    cU
    cB
    @10
    @21
    @0
    @1
    @2
    @10
    cU
    wcel
    @3
    cR
    cU
    @9
    cY
    dvrcan5.o
    @25
    unitinvcl
    3ad2antr2
    sseldi
    #
    cB
    cR
    c.x
    cZ
    @16
    @10
    dvrcan5.b
    dvrcan5.t
    ringass
    syl13anc
    @5
    @0
    @37
    @35
    @10
    wceq
    @29
    @38
    cB
    cR
    c.x
    @34
    @10
    dvrcan5.b
    dvrcan5.t
    @36
    ringlidm
    syl2anc
    3eqtr3d
    3eqtrd
    oveq2d
    @5
    @0
    @1
    @19
    @20
    @12
    @8
    wceq
    @29
    @0
    @1
    @2
    @3
    simpr1
    #
    @23
    @24
    cB
    c.dv
    cR
    c.x
    cU
    cX
    cZ
    @6
    dvrcan5.b
    dvrcan5.o
    dvrcan5.d
    dvrcan5.t
    dvrass
    syl13anc
    @5
    @1
    @2
    @13
    @11
    wceq
    @39
    @31
    cB
    c.dv
    cR
    c.x
    cU
    @9
    cX
    cY
    dvrcan5.b
    dvrcan5.t
    dvrcan5.o
    @25
    dvrcan5.d
    dvrval
    syl2anc
    3eqtr4d
end
