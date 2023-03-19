include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "subrguss.mm"
include "sselda.mm"
include "cbs.mm"
include "eqid.mm"
include "unitcl.mm"
include "adantl.mm"
include "wceq.mm"
include "subrgbas.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "cinvr.mm"
include "crg.mm"
include "subrgring.mm"
include "ringinvcl.mm"
include "sylan.mm"
include "subrginv.mm"
include "3eltr4d.mm"
include "3jca.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "cmulr.mm"
include "co.mm"
include "simpr2.mm"
include "eleqtrd.mm"
include "simpr3.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "subrgrcl.mm"
include "simpr1.mm"
include "unitlinv.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "subrg1.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "opprbas.mm"
include "opprmul.mm"
include "unitrinv.mm"
include "syl5eq.mm"
include "isunit.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem subrgunit
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  assume subrgugrp.1: |- S = ( R |`s A )
  assume subrgugrp.2: |- U = ( Unit ` R )
  assume subrgugrp.3: |- V = ( Unit ` S )
  assume subrgunit.4: |- I = ( invr ` R )


  assert |- ( A e. ( SubRing ` R ) -> ( X e. V <-> ( X e. U /\ X e. A /\ ( I ` X ) e. A ) ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    cU
    wcel
    #
    cX
    cA
    wcel
    #
    cX
    cI
    cfv
    #
    cA
    wcel
    #
    w3a
    #
    @1
    @2
    wa
    #
    @3
    @4
    @6
    @1
    cV
    cU
    cX
    cA
    cR
    cS
    cU
    cV
    subrgugrp.1
    subrgugrp.2
    subrgugrp.3
    subrguss
    sselda
    @8
    cX
    cS
    cbs
    cfv
    #
    cA
    @2
    cX
    @9
    wcel
    #
    @1
    @9
    cS
    cV
    cX
    @9
    eqid
    #
    subrgugrp.3
    unitcl
    adantl
    @1
    cA
    @9
    wceq
    #
    @2
    cA
    cR
    cS
    subrgugrp.1
    subrgbas
    #
    adantr
    #
    eleqtrrd
    @8
    cX
    cS
    cinvr
    cfv
    #
    cfv
    #
    @9
    @5
    cA
    @1
    cS
    crg
    wcel
    @2
    @16
    @9
    wcel
    cA
    cR
    cS
    subrgugrp.1
    subrgring
    @9
    cS
    cV
    @15
    cX
    subrgugrp.3
    @15
    eqid
    #
    @11
    ringinvcl
    sylan
    cA
    cR
    cS
    cV
    cI
    @15
    cX
    subrgugrp.1
    subrgunit.4
    subrgugrp.3
    @17
    subrginv
    @14
    3eltr4d
    3jca
    @1
    @7
    wa
    #
    cX
    cS
    cur
    cfv
    #
    cS
    cdsr
    cfv
    #
    wbr
    cX
    @19
    cS
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @2
    @18
    cX
    @5
    cX
    cS
    cmulr
    cfv
    #
    co
    #
    @19
    @20
    @18
    @10
    @5
    @9
    wcel
    #
    cX
    @24
    @20
    wbr
    @18
    cX
    cA
    @9
    @1
    @3
    @4
    @6
    simpr2
    @1
    @12
    @7
    @13
    adantr
    #
    eleqtrd
    #
    @18
    @5
    cA
    @9
    @1
    @3
    @4
    @6
    simpr3
    @26
    eleqtrd
    #
    @9
    @20
    cS
    @23
    cX
    @5
    @11
    @20
    eqid
    #
    @23
    eqid
    #
    dvdsrmul
    syl2anc
    @18
    @5
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    cR
    cur
    cfv
    #
    @24
    @19
    @18
    cR
    crg
    wcel
    #
    @3
    @32
    @33
    wceq
    @1
    @34
    @7
    cA
    cR
    subrgrcl
    adantr
    #
    @1
    @3
    @4
    @6
    simpr1
    #
    cR
    @31
    cU
    @33
    cI
    cX
    subrgugrp.2
    subrgunit.4
    @31
    eqid
    #
    @33
    eqid
    #
    unitlinv
    syl2anc
    @18
    @31
    @23
    @5
    cX
    @1
    @31
    @23
    wceq
    @7
    cA
    cR
    cS
    @31
    @0
    subrgugrp.1
    @37
    ressmulr
    adantr
    #
    oveqd
    @1
    @33
    @19
    wceq
    @7
    cA
    cR
    cS
    @33
    subrgugrp.1
    @38
    subrg1
    adantr
    #
    3eqtr3d
    breqtrd
    @18
    cX
    @5
    cX
    @21
    cmulr
    cfv
    #
    co
    #
    @19
    @22
    @18
    @10
    @25
    cX
    @42
    @22
    wbr
    @27
    @28
    @9
    @22
    @21
    @41
    cX
    @5
    @9
    cS
    @21
    @21
    eqid
    #
    @11
    opprbas
    @22
    eqid
    #
    @41
    eqid
    #
    dvdsrmul
    syl2anc
    @18
    @42
    cX
    @5
    @23
    co
    #
    @19
    @9
    cS
    @41
    @23
    @21
    @5
    cX
    @11
    @30
    @43
    @45
    opprmul
    @18
    cX
    @5
    @31
    co
    #
    @33
    @46
    @19
    @18
    @34
    @3
    @47
    @33
    wceq
    @35
    @36
    cR
    @31
    cU
    @33
    cI
    cX
    subrgugrp.2
    subrgunit.4
    @37
    @38
    unitrinv
    syl2anc
    @18
    @31
    @23
    cX
    @5
    @39
    oveqd
    @40
    3eqtr3d
    syl5eq
    breqtrd
    @20
    cS
    @21
    cV
    @19
    @22
    cX
    subrgugrp.3
    @19
    eqid
    @29
    @43
    @44
    isunit
    sylanbrc
    impbida
end
