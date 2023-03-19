include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cop.mm"
include "dvhvadd.mm"
include "simpl.mm"
include "xp1st.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "cv.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "eqid.mm"
include "dvhfplusr.mm"
include "adantr.mm"
include "oveqd.mm"
include "xp2nd.mm"
include "tendoplcl.mm"
include "eqeltrd.mm"
include "opelxpi.mm"
include "syl2anc.mm"

theorem dvhvaddcl
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. ( T X. E ) /\ G e. ( T X. E ) ) ) -> ( F .+ G ) e. ( T X. E ) )

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
    cG
    c.pl
    co
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
    #
    @1
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
    @5
    @8
    cT
    wcel
    #
    @11
    cE
    wcel
    @12
    @1
    wcel
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
    @13
    @0
    @4
    simpl
    #
    @2
    @14
    @0
    @3
    cF
    cT
    cE
    xp1st
    ad2antrl
    @3
    @15
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
    ltrnco
    syl3anc
    @5
    @11
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
    @17
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    cE
    @5
    c.pd
    @18
    @9
    @10
    @0
    c.pd
    @18
    wceq
    @4
    vb
    @18
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
    @18
    eqid
    #
    dvhvaddcl.p
    dvhfplusr
    adantr
    oveqd
    @5
    @0
    @9
    cE
    wcel
    #
    @10
    cE
    wcel
    #
    @19
    cE
    wcel
    @16
    @2
    @21
    @0
    @3
    cF
    cT
    cE
    xp2nd
    ad2antrl
    @3
    @22
    @0
    @2
    cG
    cT
    cE
    xp2nd
    ad2antll
    vb
    @18
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
    @20
    tendoplcl
    syl3anc
    eqeltrd
    @8
    @11
    cT
    cE
    opelxpi
    syl2anc
    eqeltrd
end
