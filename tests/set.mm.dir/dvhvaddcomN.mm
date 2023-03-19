include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "simpl.mm"
include "xp1st.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ltrncom.mm"
include "syl3anc.mm"
include "cv.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "xp2nd.mm"
include "anim12i.mm"
include "eqid.mm"
include "tendoplcom.mm"
include "3expb.mm"
include "sylan2.mm"
include "dvhfplusr.mm"
include "adantr.mm"
include "oveqd.mm"
include "3eqtr4d.mm"
include "opeq12d.mm"
include "dvhvadd.mm"
include "ancom2s.mm"

theorem dvhvaddcomN
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume dvhvaddcl.h: |- H = ( LHyp ` K )
  assume dvhvaddcl.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhvaddcl.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhvaddcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhvaddcl.d: |- D = ( Scalar ` U )
  assume dvhvaddcl.p: |- .+^ = ( +g ` D )
  assume dvhvaddcl.a: |- .+ = ( +g ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. ( T X. E ) /\ G e. ( T X. E ) ) ) -> ( F .+ G ) = ( G .+ F ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    cE
    cxp
    #
    wcel
    #
    cG
    @1
    wcel
    #
    wa
    #
    wa
    #
    cF
    c1st
    cfv
    #
    cG
    c1st
    cfv
    #
    ccom
    #
    cF
    c2nd
    cfv
    #
    cG
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    @7
    @6
    ccom
    #
    @10
    @9
    c.pd
    co
    #
    cop
    #
    cF
    cG
    c.pl
    co
    cG
    cF
    c.pl
    co
    #
    @5
    @8
    @12
    @11
    @13
    @5
    @0
    @6
    cT
    wcel
    #
    @7
    cT
    wcel
    #
    @8
    @12
    wceq
    @0
    @4
    simpl
    @2
    @16
    @0
    @3
    cF
    cT
    cE
    xp1st
    ad2antrl
    @3
    @17
    @0
    @2
    cG
    cT
    cE
    xp1st
    ad2antll
    cT
    @6
    @7
    cH
    cK
    cW
    dvhvaddcl.h
    dvhvaddcl.t
    ltrncom
    syl3anc
    @5
    @9
    @10
    va
    vb
    cE
    cE
    vc
    cT
    vc
    cv
    #
    va
    cv
    cfv
    @18
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    @10
    @9
    @19
    co
    #
    @11
    @13
    @4
    @0
    @9
    cE
    wcel
    #
    @10
    cE
    wcel
    #
    wa
    @20
    @21
    wceq
    #
    @2
    @22
    @3
    @23
    cF
    cT
    cE
    xp2nd
    cG
    cT
    cE
    xp2nd
    anim12i
    @0
    @22
    @23
    @24
    vb
    @19
    cT
    @9
    vc
    cE
    cH
    cK
    @10
    cW
    va
    dvhvaddcl.h
    dvhvaddcl.t
    dvhvaddcl.e
    @19
    eqid
    #
    tendoplcom
    3expb
    sylan2
    @5
    c.pd
    @19
    @9
    @10
    @0
    c.pd
    @19
    wceq
    @4
    vb
    @19
    c.pd
    cT
    cU
    vc
    cE
    cD
    cH
    cK
    chlt
    cW
    va
    dvhvaddcl.h
    dvhvaddcl.t
    dvhvaddcl.e
    dvhvaddcl.u
    dvhvaddcl.d
    @25
    dvhvaddcl.p
    dvhfplusr
    adantr
    #
    oveqd
    @5
    c.pd
    @19
    @10
    @9
    @26
    oveqd
    3eqtr4d
    opeq12d
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    cF
    cG
    cH
    cK
    cW
    dvhvaddcl.h
    dvhvaddcl.t
    dvhvaddcl.e
    dvhvaddcl.u
    dvhvaddcl.d
    dvhvaddcl.a
    dvhvaddcl.p
    dvhvadd
    @0
    @3
    @2
    @15
    @14
    wceq
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    cG
    cF
    cH
    cK
    cW
    dvhvaddcl.h
    dvhvaddcl.t
    dvhvaddcl.e
    dvhvaddcl.u
    dvhvaddcl.d
    dvhvaddcl.a
    dvhvaddcl.p
    dvhvadd
    ancom2s
    3eqtr4d
end
