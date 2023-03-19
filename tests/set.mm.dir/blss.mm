include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "cv.mm"
include "co.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "wceq.mm"
include "cxr.mm"
include "wi.mm"
include "blrn.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "elbl.mm"
include "cq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "qbtwnxr.mm"
include "3expia.mm"
include "syl2anc.mm"
include "cr.mm"
include "qre.mm"
include "cmin.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpll2.mm"
include "xmetsym.mm"
include "simprrl.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "cle.mm"
include "simprl.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "xrltle.mm"
include "mpd.mm"
include "xmetlecl.mm"
include "syl122anc.mm"
include "difrp.mm"
include "mpbid.mm"
include "resubcld.mm"
include "xrleid.mm"
include "syl.mm"
include "recnd.mm"
include "nncand.mm"
include "breqtrrd.mm"
include "blss2.mm"
include "syl33anc.mm"
include "simpll3.mm"
include "simprrr.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "sstrd.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "expr.mm"
include "sylan2.mm"
include "rexlimdva.mm"
include "syld.mm"
include "expimpd.mm"
include "sylbid.mm"
include "eleq2.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "3expib.mm"
include "rexlimdvv.mm"
include "3imp.mm"

theorem blss
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cP: class P
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cC: class C
  let cR: class R
  let cS: class S

  disjoint B x
  disjoint D x
  disjoint P x
  disjoint X x
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D r
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint P r
  disjoint P y
  disjoint P z
  disjoint S x
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( *Met ` X ) /\ B e. ran ( ball ` D ) /\ P e. B ) -> E. x e. RR+ ( P ( ball ` D ) x ) C_ B )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cB
    cD
    cbl
    cfv
    #
    crn
    wcel
    #
    cP
    cB
    wcel
    #
    cP
    vx
    cv
    #
    @1
    co
    #
    cB
    wss
    #
    vx
    crp
    wrex
    #
    @0
    @2
    cB
    vy
    cv
    #
    vr
    cv
    #
    @1
    co
    #
    wceq
    #
    vr
    cxr
    wrex
    vy
    cX
    wrex
    @3
    @7
    wi
    #
    vy
    cB
    cD
    cX
    vr
    blrn
    @0
    @11
    @12
    vy
    vr
    cX
    cxr
    @0
    @8
    cX
    wcel
    #
    @9
    cxr
    wcel
    #
    @11
    @12
    wi
    @0
    @13
    @14
    w3a
    #
    @12
    @11
    cP
    @10
    wcel
    #
    @5
    @10
    wss
    #
    vx
    crp
    wrex
    #
    wi
    @15
    @16
    cP
    cX
    wcel
    #
    @8
    cP
    cD
    co
    #
    @9
    clt
    wbr
    #
    wa
    @18
    cP
    cD
    @8
    @9
    cX
    elbl
    @15
    @19
    @21
    @18
    @15
    @19
    wa
    #
    @21
    @20
    vz
    cv
    #
    clt
    wbr
    #
    @23
    @9
    clt
    wbr
    #
    wa
    #
    vz
    cq
    wrex
    #
    @18
    @22
    @20
    cxr
    wcel
    #
    @14
    @21
    @27
    wi
    @22
    @0
    @13
    @19
    @28
    @0
    @13
    @14
    @19
    simpl1
    @0
    @13
    @14
    @19
    simpl2
    @15
    @19
    simpr
    @8
    cP
    cD
    cX
    xmetcl
    syl3anc
    @0
    @13
    @14
    @19
    simpl3
    @28
    @14
    @21
    @27
    vz
    @20
    @9
    qbtwnxr
    3expia
    syl2anc
    @22
    @26
    @18
    vz
    cq
    @23
    cq
    wcel
    @22
    @23
    cr
    wcel
    #
    @26
    @18
    wi
    @23
    qre
    @22
    @29
    @26
    @18
    @22
    @29
    @26
    wa
    #
    wa
    #
    @23
    cP
    @8
    cD
    co
    #
    cmin
    co
    #
    crp
    wcel
    #
    cP
    @33
    @1
    co
    #
    @10
    wss
    #
    @18
    @31
    @32
    @23
    clt
    wbr
    #
    @34
    @31
    @32
    @20
    @23
    clt
    @31
    @0
    @19
    @13
    @32
    @20
    wceq
    @0
    @13
    @14
    @19
    @30
    simpll1
    #
    @15
    @19
    @30
    simplr
    #
    @0
    @13
    @14
    @19
    @30
    simpll2
    #
    cP
    @8
    cD
    cX
    xmetsym
    syl3anc
    @22
    @29
    @24
    @25
    simprrl
    eqbrtrd
    #
    @31
    @32
    cr
    wcel
    #
    @29
    @37
    @34
    wb
    @31
    @0
    @19
    @13
    @29
    @32
    @23
    cle
    wbr
    #
    @42
    @38
    @39
    @40
    @22
    @29
    @26
    simprl
    #
    @31
    @37
    @43
    @41
    @31
    @32
    cxr
    wcel
    #
    @23
    cxr
    wcel
    #
    @37
    @43
    wi
    @31
    @0
    @19
    @13
    @45
    @38
    @39
    @40
    cP
    @8
    cD
    cX
    xmetcl
    syl3anc
    #
    @29
    @46
    @22
    @26
    @23
    rexr
    ad2antrl
    #
    @32
    @23
    xrltle
    syl2anc
    mpd
    cP
    @8
    @23
    cD
    cX
    xmetlecl
    syl122anc
    #
    @44
    @32
    @23
    difrp
    syl2anc
    mpbid
    @31
    @35
    @8
    @23
    @1
    co
    #
    @10
    @31
    @0
    @19
    @13
    @33
    cr
    wcel
    @29
    @32
    @23
    @33
    cmin
    co
    #
    cle
    wbr
    @35
    @50
    wss
    @38
    @39
    @40
    @31
    @23
    @32
    @44
    @49
    resubcld
    @44
    @31
    @32
    @32
    @51
    cle
    @31
    @45
    @32
    @32
    cle
    wbr
    @47
    @32
    xrleid
    syl
    @31
    @23
    @32
    @31
    @23
    @44
    recnd
    @31
    @32
    @49
    recnd
    nncand
    breqtrrd
    cD
    cP
    @8
    @33
    @23
    cX
    blss2
    syl33anc
    @31
    @0
    @13
    @46
    @14
    @23
    @9
    cle
    wbr
    #
    @50
    @10
    wss
    @38
    @40
    @48
    @0
    @13
    @14
    @19
    @30
    simpll3
    #
    @31
    @25
    @52
    @22
    @29
    @24
    @25
    simprrr
    @31
    @46
    @14
    @25
    @52
    wi
    @48
    @53
    @23
    @9
    xrltle
    syl2anc
    mpd
    cD
    @8
    @23
    @9
    cX
    ssbl
    syl221anc
    sstrd
    @17
    @36
    vx
    @33
    crp
    @4
    @33
    wceq
    @5
    @35
    @10
    @4
    @33
    cP
    @1
    oveq2
    sseq1d
    rspcev
    syl2anc
    expr
    sylan2
    rexlimdva
    syld
    expimpd
    sylbid
    @11
    @3
    @16
    @7
    @18
    cB
    @10
    cP
    eleq2
    @11
    @6
    @17
    vx
    crp
    cB
    @10
    @5
    sseq2
    rexbidv
    imbi12d
    syl5ibrcom
    3expib
    rexlimdvv
    sylbid
    3imp
end
