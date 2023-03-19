include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "tgrpbase.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "wceq.mm"
include "a1i.mm"
include "w3a.mm"
include "co.mm"
include "ccom.mm"
include "tgrpov.mm"
include "3expa.mm"
include "3impb.mm"
include "ltrnco.mm"
include "eqeltrd.mm"
include "coass.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "syl112anc.mm"
include "oveq1d.mm"
include "simpl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "idltrn.mm"
include "adantr.mm"
include "simpr.mm"
include "wf1o.mm"
include "wf.mm"
include "ltrn1o.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "ltrncnv.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "isgrpd.mm"

theorem tgrpgrplem
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  let cY: class Y
  assume tgrpset.h: |- H = ( LHyp ` K )
  assume tgrpset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tgrpset.g: |- G = ( ( TGrp ` K ) ` W )
  assume tgrp.o: |- .+ = ( +g ` G )
  assume tgrp.b: |- B = ( Base ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> G e. Grp )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    vx
    vy
    vz
    cT
    c.pl
    cG
    vx
    cv
    #
    ccnv
    #
    cid
    cB
    cres
    #
    @2
    cG
    cbs
    cfv
    #
    cT
    @6
    cT
    cG
    cH
    cK
    chlt
    cW
    tgrpset.h
    tgrpset.t
    tgrpset.g
    @6
    eqid
    tgrpbase
    eqcomd
    c.pl
    cG
    cplusg
    cfv
    wceq
    @2
    tgrp.o
    a1i
    @2
    @3
    cT
    wcel
    #
    vy
    cv
    #
    cT
    wcel
    #
    w3a
    @3
    @8
    c.pl
    co
    #
    @3
    @8
    ccom
    #
    cT
    @2
    @7
    @9
    @10
    @11
    wceq
    #
    @0
    @1
    @7
    @9
    wa
    @12
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @3
    @8
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    #
    3expa
    3impb
    cT
    @3
    @8
    cH
    cK
    cW
    tgrpset.h
    tgrpset.t
    ltrnco
    #
    eqeltrd
    @2
    @7
    @9
    vz
    cv
    #
    cT
    wcel
    #
    w3a
    #
    wa
    #
    @11
    @15
    ccom
    #
    @3
    @8
    @15
    ccom
    #
    ccom
    #
    @10
    @15
    c.pl
    co
    #
    @3
    @8
    @15
    c.pl
    co
    #
    c.pl
    co
    #
    @3
    @8
    @15
    coass
    @18
    @22
    @11
    @15
    c.pl
    co
    #
    @19
    @18
    @10
    @11
    @15
    c.pl
    @18
    @0
    @1
    @7
    @9
    @12
    @0
    @1
    @17
    simpll
    #
    @0
    @1
    @17
    simplr
    #
    @2
    @7
    @9
    @16
    simpr1
    #
    @2
    @7
    @9
    @16
    simpr2
    #
    @13
    syl112anc
    oveq1d
    @18
    @0
    @1
    @11
    cT
    wcel
    #
    @16
    @25
    @19
    wceq
    @26
    @27
    @18
    @2
    @7
    @9
    @30
    @2
    @17
    simpl
    #
    @28
    @29
    @14
    syl3anc
    @2
    @7
    @9
    @16
    simpr3
    #
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @11
    @15
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    syl112anc
    eqtrd
    @18
    @24
    @3
    @20
    c.pl
    co
    #
    @21
    @18
    @23
    @20
    @3
    c.pl
    @18
    @0
    @1
    @9
    @16
    @23
    @20
    wceq
    @26
    @27
    @29
    @32
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @8
    @15
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    syl112anc
    oveq2d
    @18
    @0
    @1
    @7
    @20
    cT
    wcel
    #
    @33
    @21
    wceq
    @26
    @27
    @28
    @18
    @2
    @9
    @16
    @34
    @31
    @29
    @32
    cT
    @8
    @15
    cH
    cK
    cW
    tgrpset.h
    tgrpset.t
    ltrnco
    syl3anc
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @3
    @20
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    syl112anc
    eqtrd
    3eqtr4a
    cB
    cT
    cH
    cK
    cW
    tgrp.b
    tgrpset.h
    tgrpset.t
    idltrn
    #
    @2
    @7
    wa
    #
    @5
    @3
    c.pl
    co
    #
    @5
    @3
    ccom
    #
    @3
    @36
    @0
    @1
    @5
    cT
    wcel
    #
    @7
    @37
    @38
    wceq
    @0
    @1
    @7
    simpll
    #
    @0
    @1
    @7
    simplr
    #
    @2
    @39
    @7
    @35
    adantr
    @2
    @7
    simpr
    #
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @5
    @3
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    syl112anc
    @36
    cB
    cB
    @3
    wf1o
    #
    cB
    cB
    @3
    wf
    @38
    @3
    wceq
    cB
    cT
    @3
    cH
    cK
    chlt
    cW
    tgrp.b
    tgrpset.h
    tgrpset.t
    ltrn1o
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
    eqtrd
    cT
    @3
    cH
    cK
    cW
    tgrpset.h
    tgrpset.t
    ltrncnv
    #
    @36
    @4
    @3
    c.pl
    co
    #
    @4
    @3
    ccom
    #
    @5
    @36
    @0
    @1
    @4
    cT
    wcel
    @7
    @46
    @47
    wceq
    @40
    @41
    @45
    @42
    c.pl
    cT
    cG
    cH
    cK
    chlt
    cW
    @4
    @3
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpov
    syl112anc
    @36
    @43
    @47
    @5
    wceq
    @44
    cB
    cB
    @3
    f1ococnv1
    syl
    eqtrd
    isgrpd
end
