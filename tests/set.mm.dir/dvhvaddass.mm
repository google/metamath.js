include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "w3a.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cop.mm"
include "coass.mm"
include "wceq.mm"
include "dvhvadd.mm"
include "3adantr3.mm"
include "fveq2d.mm"
include "fvex.mm"
include "coex.mm"
include "ovex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "coeq1d.mm"
include "3adantr1.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "xp2nd.mm"
include "3anim123i.mm"
include "cgrp.mm"
include "cbs.mm"
include "cdr.mm"
include "cedring.mm"
include "eqid.mm"
include "dvhsca.mm"
include "erngdv.mm"
include "eqeltrd.mm"
include "drnggrp.mm"
include "syl.mm"
include "adantr.mm"
include "simpr1.mm"
include "dvhbase.mm"
include "eleqtrrd.mm"
include "simpr2.mm"
include "simpr3.mm"
include "grpass.mm"
include "syl13anc.mm"
include "sylan2.mm"
include "op2nd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "opeq12d.mm"
include "simpl.mm"
include "dvhvaddcl.mm"
include "syl12anc.mm"

theorem dvhvaddass
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. ( T X. E ) /\ G e. ( T X. E ) /\ I e. ( T X. E ) ) ) -> ( ( F .+ G ) .+ I ) = ( F .+ ( G .+ I ) ) )

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
    cI
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cF
    cG
    c.pl
    co
    #
    c1st
    cfv
    #
    cI
    c1st
    cfv
    #
    ccom
    #
    @7
    c2nd
    cfv
    #
    cI
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    cF
    c1st
    cfv
    #
    cG
    cI
    c.pl
    co
    #
    c1st
    cfv
    #
    ccom
    #
    cF
    c2nd
    cfv
    #
    @16
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    @7
    cI
    c.pl
    co
    #
    cF
    @16
    c.pl
    co
    #
    @6
    @10
    @18
    @13
    @21
    @6
    @15
    cG
    c1st
    cfv
    #
    ccom
    #
    @9
    ccom
    @15
    @25
    @9
    ccom
    #
    ccom
    @10
    @18
    @15
    @25
    @9
    coass
    @6
    @8
    @26
    @9
    @6
    @8
    @26
    @19
    cG
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    c1st
    cfv
    @26
    @6
    @7
    @30
    c1st
    @0
    @2
    @3
    @7
    @30
    wceq
    @4
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
    3adantr3
    #
    fveq2d
    @26
    @29
    @15
    @25
    cF
    c1st
    fvex
    cG
    c1st
    fvex
    #
    coex
    #
    @19
    @28
    c.pd
    ovex
    #
    op1st
    syl6eq
    coeq1d
    @6
    @17
    @27
    @15
    @6
    @17
    @27
    @28
    @12
    c.pd
    co
    #
    cop
    #
    c1st
    cfv
    @27
    @6
    @16
    @36
    c1st
    @0
    @3
    @4
    @16
    @36
    wceq
    @2
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    cG
    cI
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
    3adantr1
    #
    fveq2d
    @27
    @35
    @25
    @9
    @32
    cI
    c1st
    fvex
    coex
    #
    @28
    @12
    c.pd
    ovex
    #
    op1st
    syl6eq
    coeq2d
    3eqtr4a
    @6
    @29
    @12
    c.pd
    co
    #
    @19
    @35
    c.pd
    co
    #
    @13
    @21
    @5
    @0
    @19
    cE
    wcel
    #
    @28
    cE
    wcel
    #
    @12
    cE
    wcel
    #
    w3a
    #
    @40
    @41
    wceq
    #
    @2
    @42
    @3
    @43
    @4
    @44
    cF
    cT
    cE
    xp2nd
    cG
    cT
    cE
    xp2nd
    cI
    cT
    cE
    xp2nd
    3anim123i
    @0
    @45
    wa
    #
    cD
    cgrp
    wcel
    #
    @19
    cD
    cbs
    cfv
    #
    wcel
    @28
    @49
    wcel
    @12
    @49
    wcel
    @46
    @0
    @48
    @45
    @0
    cD
    cdr
    wcel
    @48
    @0
    cD
    cW
    cK
    cedring
    cfv
    cfv
    #
    cdr
    @50
    cU
    cD
    cH
    cK
    cW
    chlt
    dvhvaddcl.h
    @50
    eqid
    #
    dvhvaddcl.u
    dvhvaddcl.d
    dvhsca
    @50
    cH
    cK
    cW
    dvhvaddcl.h
    @51
    erngdv
    eqeltrd
    cD
    drnggrp
    syl
    adantr
    @47
    @19
    cE
    @49
    @0
    @42
    @43
    @44
    simpr1
    @0
    @49
    cE
    wceq
    @45
    @49
    cU
    cE
    cD
    cH
    cK
    cW
    chlt
    dvhvaddcl.h
    dvhvaddcl.e
    dvhvaddcl.u
    dvhvaddcl.d
    @49
    eqid
    #
    dvhbase
    adantr
    #
    eleqtrrd
    @47
    @28
    cE
    @49
    @0
    @42
    @43
    @44
    simpr2
    @53
    eleqtrrd
    @47
    @12
    cE
    @49
    @0
    @42
    @43
    @44
    simpr3
    @53
    eleqtrrd
    @49
    c.pd
    cD
    @19
    @28
    @12
    @52
    dvhvaddcl.p
    grpass
    syl13anc
    sylan2
    @6
    @11
    @29
    @12
    c.pd
    @6
    @11
    @30
    c2nd
    cfv
    @29
    @6
    @7
    @30
    c2nd
    @31
    fveq2d
    @26
    @29
    @33
    @34
    op2nd
    syl6eq
    oveq1d
    @6
    @20
    @35
    @19
    c.pd
    @6
    @20
    @36
    c2nd
    cfv
    @35
    @6
    @16
    @36
    c2nd
    @37
    fveq2d
    @27
    @35
    @38
    @39
    op2nd
    syl6eq
    oveq2d
    3eqtr4d
    opeq12d
    @6
    @0
    @7
    @1
    wcel
    #
    @4
    @23
    @14
    wceq
    @0
    @5
    simpl
    #
    @0
    @2
    @3
    @54
    @4
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
    dvhvaddcl.p
    dvhvaddcl.a
    dvhvaddcl
    3adantr3
    @0
    @2
    @3
    @4
    simpr3
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    @7
    cI
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
    syl12anc
    @6
    @0
    @2
    @16
    @1
    wcel
    #
    @24
    @22
    wceq
    @55
    @0
    @2
    @3
    @4
    simpr1
    @0
    @3
    @4
    @56
    @2
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    cG
    cI
    cH
    cK
    cW
    dvhvaddcl.h
    dvhvaddcl.t
    dvhvaddcl.e
    dvhvaddcl.u
    dvhvaddcl.d
    dvhvaddcl.p
    dvhvaddcl.a
    dvhvaddcl
    3adantr1
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    cF
    @16
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
    syl12anc
    3eqtr4d
end
