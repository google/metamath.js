include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "simpl1.mm"
include "assaring.mm"
include "syl.mm"
include "adantl.mm"
include "syl5eqelr.mm"
include "jca.mm"
include "simpl3.mm"
include "simpl2.mm"
include "issubrg.mm"
include "sylanbrc.mm"
include "clmod.mm"
include "assalmod.mm"
include "wb.mm"
include "islss3.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "csca.mm"
include "cbs.mm"
include "cvsca.mm"
include "cmulr.mm"
include "wceq.mm"
include "subrgss.mm"
include "ad2antrl.mm"
include "ressbas2.mm"
include "eqid.mm"
include "resssca.mm"
include "eqidd.mm"
include "ressvsca.mm"
include "ressmulr.mm"
include "simpr.mm"
include "lsslmod.mm"
include "syl2an.mm"
include "subrgring.mm"
include "ccrg.mm"
include "assasca.mm"
include "adantr.mm"
include "cv.mm"
include "simpll.mm"
include "simpr1.mm"
include "simpr2.mm"
include "sseldd.mm"
include "simpr3.mm"
include "assaass.mm"
include "syl13anc.mm"
include "assaassr.mm"
include "isassad.mm"
include "3ad2antl1.mm"
include "impbida.mm"

theorem issubassa
  let cA: class A
  let cS: class S
  let c.1: class .1.
  let cL: class L
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume issubassa.s: |- S = ( W |`s A )
  assume issubassa.l: |- L = ( LSubSp ` W )
  assume issubassa.v: |- V = ( Base ` W )
  assume issubassa.o: |- .1. = ( 1r ` W )


  assert |- ( ( W e. AssAlg /\ .1. e. A /\ A C_ V ) -> ( S e. AssAlg <-> ( A e. ( SubRing ` W ) /\ A e. L ) ) )

  proof
    cW
    casa
    wcel
    #
    c.1
    cA
    wcel
    #
    cA
    cV
    wss
    #
    w3a
    #
    cS
    casa
    wcel
    #
    cA
    cW
    csubrg
    cfv
    #
    wcel
    #
    cA
    cL
    wcel
    #
    wa
    #
    @3
    @4
    wa
    #
    @6
    @7
    @9
    cW
    crg
    wcel
    #
    cW
    cA
    cress
    co
    #
    crg
    wcel
    #
    wa
    @2
    @1
    wa
    @6
    @9
    @10
    @12
    @9
    @0
    @10
    @0
    @1
    @2
    @4
    simpl1
    #
    cW
    assaring
    syl
    @9
    @11
    cS
    crg
    issubassa.s
    @4
    cS
    crg
    wcel
    #
    @3
    cS
    assaring
    adantl
    syl5eqelr
    jca
    @9
    @2
    @1
    @0
    @1
    @2
    @4
    simpl3
    #
    @0
    @1
    @2
    @4
    simpl2
    jca
    cA
    cV
    cW
    c.1
    issubassa.v
    issubassa.o
    issubrg
    sylanbrc
    @9
    @7
    @2
    cS
    clmod
    wcel
    #
    @15
    @4
    @16
    @3
    cS
    assalmod
    adantl
    @9
    @0
    cW
    clmod
    wcel
    #
    @7
    @2
    @16
    wa
    wb
    @13
    cW
    assalmod
    #
    cL
    cA
    cV
    cW
    cS
    issubassa.s
    issubassa.v
    issubassa.l
    islss3
    3syl
    mpbir2and
    jca
    @0
    @1
    @8
    @4
    @2
    @0
    @8
    wa
    #
    vy
    vz
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cvsca
    cfv
    #
    cW
    cmulr
    cfv
    #
    @20
    cA
    cS
    vx
    @19
    @2
    cA
    cS
    cbs
    cfv
    wceq
    @6
    @2
    @0
    @7
    cA
    cV
    cW
    issubassa.v
    subrgss
    ad2antrl
    #
    cA
    cV
    cS
    cW
    issubassa.s
    issubassa.v
    ressbas2
    syl
    @6
    @20
    cS
    csca
    cfv
    wceq
    @0
    @7
    cA
    @20
    cW
    cS
    @5
    issubassa.s
    @20
    eqid
    #
    resssca
    ad2antrl
    @19
    @21
    eqidd
    @6
    @22
    cS
    cvsca
    cfv
    wceq
    @0
    @7
    cA
    @22
    cW
    cS
    @5
    issubassa.s
    @22
    eqid
    #
    ressvsca
    ad2antrl
    @6
    @23
    cS
    cmulr
    cfv
    wceq
    @0
    @7
    cA
    cW
    cS
    @23
    @5
    issubassa.s
    @23
    eqid
    #
    ressmulr
    ad2antrl
    @0
    @17
    @7
    @16
    @8
    @18
    @6
    @7
    simpr
    cL
    cA
    cW
    cS
    issubassa.s
    issubassa.l
    lsslmod
    syl2an
    @6
    @14
    @0
    @7
    cA
    cW
    cS
    issubassa.s
    subrgring
    ad2antrl
    @0
    @20
    ccrg
    wcel
    @8
    @20
    cW
    @25
    assasca
    adantr
    @19
    vx
    cv
    #
    @21
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    wa
    #
    @0
    @29
    @30
    cV
    wcel
    #
    @32
    cV
    wcel
    #
    @28
    @30
    @22
    co
    @32
    @23
    co
    @28
    @30
    @32
    @23
    co
    @22
    co
    #
    wceq
    @0
    @8
    @34
    simpll
    #
    @19
    @29
    @31
    @33
    simpr1
    #
    @35
    cA
    cV
    @30
    @19
    @2
    @34
    @24
    adantr
    #
    @19
    @29
    @31
    @33
    simpr2
    sseldd
    #
    @35
    cA
    cV
    @32
    @41
    @19
    @29
    @31
    @33
    simpr3
    sseldd
    #
    @28
    @21
    @22
    @23
    @20
    cV
    cW
    @30
    @32
    issubassa.v
    @25
    @21
    eqid
    #
    @26
    @27
    assaass
    syl13anc
    @35
    @0
    @29
    @36
    @37
    @30
    @28
    @32
    @22
    co
    @23
    co
    @38
    wceq
    @39
    @40
    @42
    @43
    @28
    @21
    @22
    @23
    @20
    cV
    cW
    @30
    @32
    issubassa.v
    @25
    @44
    @26
    @27
    assaassr
    syl13anc
    isassad
    3ad2antl1
    impbida
end
