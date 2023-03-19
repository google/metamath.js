include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccnv.mm"
include "c2nd.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "eqid.mm"
include "dvhvbase.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "wceq.mm"
include "a1i.mm"
include "co.mm"
include "dvhvaddcl.mm"
include "3impb.mm"
include "dvhvaddass.mm"
include "idltrn.mm"
include "cgrp.mm"
include "cdr.mm"
include "cedring.mm"
include "dvhsca.mm"
include "erngdv.mm"
include "eqeltrd.mm"
include "drnggrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "dvhbase.mm"
include "eleqtrd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "ccom.mm"
include "simpl.mm"
include "adantr.mm"
include "xp1st.mm"
include "adantl.mm"
include "xp2nd.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "wf1o.mm"
include "wf.mm"
include "ltrn1o.mm"
include "syldan.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "grplid.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "1st2nd2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ltrncnv.mm"
include "grpinvcl.mm"
include "f1ococnv1.mm"
include "grplinv.mm"
include "isgrpd.mm"

theorem dvhgrp
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vt: setvar t
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let c.x: class .x.
  let c.xp: class .X.
  assume dvhgrp.b: |- B = ( Base ` K )
  assume dvhgrp.h: |- H = ( LHyp ` K )
  assume dvhgrp.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhgrp.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhgrp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhgrp.d: |- D = ( Scalar ` U )
  assume dvhgrp.p: |- .+^ = ( +g ` D )
  assume dvhgrp.a: |- .+ = ( +g ` U )
  assume dvhgrp.o: |- .0. = ( 0g ` D )
  assume dvhgrp.i: |- I = ( invg ` D )


  assert |- ( ( K e. HL /\ W e. H ) -> U e. Grp )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vf
    vg
    vh
    cT
    cE
    cxp
    #
    c.pl
    cU
    vf
    cv
    #
    c1st
    cfv
    #
    ccnv
    #
    @2
    c2nd
    cfv
    #
    cI
    cfv
    #
    cop
    #
    cid
    cB
    cres
    #
    c.0
    cop
    #
    @0
    cU
    cbs
    cfv
    #
    @1
    cT
    cU
    cE
    cH
    cK
    @10
    cW
    chlt
    dvhgrp.h
    dvhgrp.t
    dvhgrp.e
    dvhgrp.u
    @10
    eqid
    dvhvbase
    eqcomd
    c.pl
    cU
    cplusg
    cfv
    wceq
    @0
    dvhgrp.a
    a1i
    @0
    @2
    @1
    wcel
    #
    vg
    cv
    #
    @1
    wcel
    @2
    @12
    c.pl
    co
    @1
    wcel
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    @2
    @12
    cH
    cK
    cW
    dvhgrp.h
    dvhgrp.t
    dvhgrp.e
    dvhgrp.u
    dvhgrp.d
    dvhgrp.p
    dvhgrp.a
    dvhvaddcl
    3impb
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    @2
    @12
    cH
    vh
    cv
    cK
    cW
    dvhgrp.h
    dvhgrp.t
    dvhgrp.e
    dvhgrp.u
    dvhgrp.d
    dvhgrp.p
    dvhgrp.a
    dvhvaddass
    @0
    @8
    cT
    wcel
    #
    c.0
    cE
    wcel
    #
    @9
    @1
    wcel
    cB
    cT
    cH
    cK
    cW
    dvhgrp.b
    dvhgrp.h
    dvhgrp.t
    idltrn
    #
    @0
    c.0
    cD
    cbs
    cfv
    #
    cE
    @0
    cD
    cgrp
    wcel
    #
    c.0
    @16
    wcel
    @0
    cD
    cdr
    wcel
    @17
    @0
    cD
    cW
    cK
    cedring
    cfv
    cfv
    #
    cdr
    @18
    cU
    cD
    cH
    cK
    cW
    chlt
    dvhgrp.h
    @18
    eqid
    #
    dvhgrp.u
    dvhgrp.d
    dvhsca
    @18
    cH
    cK
    cW
    dvhgrp.h
    @19
    erngdv
    eqeltrd
    cD
    drnggrp
    syl
    #
    @16
    cD
    c.0
    @16
    eqid
    #
    dvhgrp.o
    grpidcl
    syl
    @16
    cU
    cE
    cD
    cH
    cK
    cW
    chlt
    dvhgrp.h
    dvhgrp.e
    dvhgrp.u
    dvhgrp.d
    @21
    dvhbase
    #
    eleqtrd
    #
    @8
    c.0
    cT
    cE
    opelxpi
    syl2anc
    @0
    @11
    wa
    #
    @9
    @3
    @5
    cop
    #
    c.pl
    co
    #
    @25
    @9
    @2
    c.pl
    co
    @2
    @24
    @26
    @8
    @3
    ccom
    #
    c.0
    @5
    c.pd
    co
    #
    cop
    #
    @25
    @24
    @0
    @13
    @14
    @3
    cT
    wcel
    #
    @5
    cE
    wcel
    #
    @26
    @29
    wceq
    @0
    @11
    simpl
    #
    @0
    @13
    @11
    @15
    adantr
    @0
    @14
    @11
    @23
    adantr
    @11
    @30
    @0
    @2
    cT
    cE
    xp1st
    adantl
    #
    @11
    @31
    @0
    @2
    cT
    cE
    xp2nd
    adantl
    #
    cD
    c.pl
    c.pd
    c.0
    @5
    cT
    cU
    cE
    @8
    @3
    cH
    cK
    cW
    dvhgrp.h
    dvhgrp.t
    dvhgrp.e
    dvhgrp.u
    dvhgrp.d
    dvhgrp.a
    dvhgrp.p
    dvhopvadd
    syl122anc
    @24
    @27
    @3
    @28
    @5
    @24
    cB
    cB
    @3
    wf1o
    #
    cB
    cB
    @3
    wf
    @27
    @3
    wceq
    @0
    @11
    @30
    @35
    @33
    cB
    cT
    @3
    cH
    cK
    chlt
    cW
    dvhgrp.b
    dvhgrp.h
    dvhgrp.t
    ltrn1o
    syldan
    #
    cB
    cB
    @3
    f1of
    cB
    cB
    @3
    fcoi2
    3syl
    @24
    @17
    @5
    @16
    wcel
    #
    @28
    @5
    wceq
    @0
    @17
    @11
    @20
    adantr
    #
    @24
    @5
    cE
    @16
    @34
    @0
    @16
    cE
    wceq
    @11
    @22
    adantr
    #
    eleqtrrd
    #
    @16
    c.pd
    cD
    @5
    c.0
    @21
    dvhgrp.p
    dvhgrp.o
    grplid
    syl2anc
    opeq12d
    eqtrd
    @24
    @2
    @25
    @9
    c.pl
    @11
    @2
    @25
    wceq
    @0
    @2
    cT
    cE
    1st2nd2
    adantl
    #
    oveq2d
    @41
    3eqtr4d
    @24
    @4
    cT
    wcel
    #
    @6
    cE
    wcel
    #
    @7
    @1
    wcel
    @0
    @11
    @30
    @42
    @33
    cT
    @3
    cH
    cK
    cW
    dvhgrp.h
    dvhgrp.t
    ltrncnv
    syldan
    #
    @24
    @6
    @16
    cE
    @24
    @17
    @37
    @6
    @16
    wcel
    @38
    @40
    @16
    cD
    cI
    @5
    @21
    dvhgrp.i
    grpinvcl
    syl2anc
    @39
    eleqtrd
    #
    @4
    @6
    cT
    cE
    opelxpi
    syl2anc
    @24
    @7
    @2
    c.pl
    co
    @7
    @25
    c.pl
    co
    #
    @9
    @24
    @2
    @25
    @7
    c.pl
    @41
    oveq2d
    @24
    @46
    @4
    @3
    ccom
    #
    @6
    @5
    c.pd
    co
    #
    cop
    #
    @9
    @24
    @0
    @42
    @43
    @30
    @31
    @46
    @49
    wceq
    @32
    @44
    @45
    @33
    @34
    cD
    c.pl
    c.pd
    @6
    @5
    cT
    cU
    cE
    @4
    @3
    cH
    cK
    cW
    dvhgrp.h
    dvhgrp.t
    dvhgrp.e
    dvhgrp.u
    dvhgrp.d
    dvhgrp.a
    dvhgrp.p
    dvhopvadd
    syl122anc
    @24
    @47
    @8
    @48
    c.0
    @24
    @35
    @47
    @8
    wceq
    @36
    cB
    cB
    @3
    f1ococnv1
    syl
    @24
    @17
    @37
    @48
    c.0
    wceq
    @38
    @40
    @16
    c.pd
    cD
    cI
    @5
    c.0
    @21
    dvhgrp.p
    dvhgrp.o
    dvhgrp.i
    grplinv
    syl2anc
    opeq12d
    eqtrd
    eqtrd
    isgrpd
end
