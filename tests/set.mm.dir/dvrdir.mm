include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "unitss.mm"
include "simpr3.mm"
include "eqid.mm"
include "unitinvcl.mm"
include "syldan.mm"
include "sseldi.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "dvrval.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem dvrdir
  let cB: class B
  let c.dv: class ./
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvrdir.b: |- B = ( Base ` R )
  assume dvrdir.u: |- U = ( Unit ` R )
  assume dvrdir.p: |- .+ = ( +g ` R )
  assume dvrdir.t: |- ./ = ( /r ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B /\ Z e. U ) ) -> ( ( X .+ Y ) ./ Z ) = ( ( X ./ Z ) .+ ( Y ./ Z ) ) )

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
    cB
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
    cY
    c.pl
    co
    #
    cZ
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    @8
    @9
    co
    #
    cY
    @8
    @9
    co
    #
    c.pl
    co
    #
    @6
    cZ
    c.dv
    co
    #
    cX
    cZ
    c.dv
    co
    #
    cY
    cZ
    c.dv
    co
    #
    c.pl
    co
    @5
    @0
    @1
    @2
    @8
    cB
    wcel
    @10
    @13
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @5
    cU
    cB
    @8
    cB
    cR
    cU
    dvrdir.b
    dvrdir.u
    unitss
    @0
    @4
    @3
    @8
    cU
    wcel
    @0
    @1
    @2
    @3
    simpr3
    #
    cR
    cU
    @7
    cZ
    dvrdir.u
    @7
    eqid
    #
    unitinvcl
    syldan
    sseldi
    cB
    c.pl
    cR
    @9
    cX
    cY
    @8
    dvrdir.b
    dvrdir.p
    @9
    eqid
    #
    ringdir
    syl13anc
    @5
    @6
    cB
    wcel
    #
    @3
    @14
    @10
    wceq
    @5
    cR
    cgrp
    wcel
    #
    @1
    @2
    @22
    @0
    @23
    @4
    cR
    ringgrp
    adantr
    @17
    @18
    cB
    c.pl
    cR
    cX
    cY
    dvrdir.b
    dvrdir.p
    grpcl
    syl3anc
    @19
    cB
    c.dv
    cR
    @9
    cU
    @7
    @6
    cZ
    dvrdir.b
    @21
    dvrdir.u
    @20
    dvrdir.t
    dvrval
    syl2anc
    @5
    @15
    @11
    @16
    @12
    c.pl
    @5
    @1
    @3
    @15
    @11
    wceq
    @17
    @19
    cB
    c.dv
    cR
    @9
    cU
    @7
    cX
    cZ
    dvrdir.b
    @21
    dvrdir.u
    @20
    dvrdir.t
    dvrval
    syl2anc
    @5
    @2
    @3
    @16
    @12
    wceq
    @18
    @19
    cB
    c.dv
    cR
    @9
    cU
    @7
    cY
    cZ
    dvrdir.b
    @21
    dvrdir.u
    @20
    dvrdir.t
    dvrval
    syl2anc
    oveq12d
    3eqtr4d
end
