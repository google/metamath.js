include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cbs.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "dmatmat.mm"
include "imp.mm"
include "adantrr.mm"
include "matecld.mm"
include "adantrl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ring0cl.mm"
include "adantl.mm"
include "adantr.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "cvv.mm"
include "eqidd.mm"
include "eqeq12.mm"
include "oveq12.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "simplrl.mm"
include "simplrr.mm"
include "ovex.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "ifnefalse.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "dmatmul.mm"
include "dmatval.mm"
include "3eltr4d.mm"

theorem dmatmulcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( X e. D /\ Y e. D ) ) -> ( X ( .r ` A ) Y ) e. D )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    cN
    cN
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    @7
    @8
    cX
    co
    #
    @7
    @8
    cY
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @16
    @17
    vm
    cv
    #
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    cX
    cY
    cA
    cmulr
    cfv
    co
    cD
    @6
    @15
    cB
    wcel
    @18
    @16
    @17
    @15
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @15
    @24
    wcel
    @6
    vx
    vy
    cA
    cB
    @14
    cR
    cR
    cbs
    cfv
    #
    cN
    crg
    dmatid.a
    @29
    eqid
    #
    dmatid.b
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    #
    @6
    @7
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    w3a
    #
    @9
    @13
    c.0
    @29
    @34
    @1
    @10
    @29
    wcel
    @11
    @29
    wcel
    @13
    @29
    wcel
    @6
    @32
    @1
    @33
    @31
    3ad2ant1
    @34
    cA
    cA
    cbs
    cfv
    #
    cR
    @7
    @8
    @29
    cX
    cN
    dmatid.a
    @30
    @35
    eqid
    #
    @6
    @32
    @33
    simp2
    #
    @6
    @32
    @33
    simp3
    #
    @6
    @32
    cX
    @35
    wcel
    #
    @33
    @2
    @3
    @39
    @4
    @2
    @3
    @39
    cA
    @35
    cD
    cR
    cX
    cN
    crg
    c.0
    dmatid.a
    @36
    dmatid.0
    dmatid.d
    dmatmat
    imp
    adantrr
    3ad2ant1
    matecld
    @34
    cA
    @35
    cR
    @7
    @8
    @29
    cY
    cN
    dmatid.a
    @30
    @36
    @37
    @38
    @6
    @32
    cY
    @35
    wcel
    #
    @33
    @2
    @4
    @40
    @3
    @2
    @4
    @40
    cA
    @35
    cD
    cR
    cY
    cN
    crg
    c.0
    dmatid.a
    @36
    dmatid.0
    dmatid.d
    dmatmat
    imp
    adantrl
    3ad2ant1
    matecld
    @29
    cR
    @12
    @10
    @11
    @30
    @12
    eqid
    ringcl
    syl3anc
    @6
    @32
    c.0
    @29
    wcel
    #
    @33
    @2
    @41
    @5
    @1
    @41
    @0
    @29
    cR
    c.0
    @30
    dmatid.0
    ring0cl
    adantl
    adantr
    3ad2ant1
    ifcld
    matbas2d
    @6
    @27
    vi
    vj
    cN
    cN
    @6
    @16
    cN
    wcel
    #
    @17
    cN
    wcel
    #
    wa
    wa
    #
    @18
    @26
    @44
    @18
    wa
    #
    @25
    @16
    @17
    wceq
    #
    @16
    @17
    cX
    co
    #
    @16
    @17
    cY
    co
    #
    @12
    co
    #
    c.0
    cif
    #
    c.0
    @45
    vx
    vy
    @16
    @17
    cN
    cN
    @14
    @50
    @15
    cvv
    @45
    @15
    eqidd
    @7
    @16
    wceq
    @8
    @17
    wceq
    wa
    #
    @14
    @50
    wceq
    @45
    @51
    @9
    @46
    @13
    @49
    c.0
    @7
    @16
    @8
    @17
    eqeq12
    @51
    @10
    @47
    @11
    @48
    @12
    @7
    @16
    @8
    @17
    cX
    oveq12
    @7
    @16
    @8
    @17
    cY
    oveq12
    oveq12d
    ifbieq1d
    adantl
    @6
    @42
    @43
    @18
    simplrl
    @6
    @42
    @43
    @18
    simplrr
    @50
    cvv
    wcel
    @45
    @46
    @49
    c.0
    @47
    @48
    @12
    ovex
    c.0
    cR
    c0g
    cfv
    cvv
    dmatid.0
    cR
    c0g
    fvex
    eqeltri
    ifex
    a1i
    ovmpt2d
    @18
    @50
    c.0
    wceq
    @44
    @16
    @17
    @49
    c.0
    ifnefalse
    adantl
    eqtrd
    ex
    ralrimivva
    @23
    @28
    vm
    @15
    cB
    @19
    @15
    wceq
    #
    @22
    @27
    vi
    vj
    cN
    cN
    @52
    @21
    @26
    @18
    @52
    @20
    @25
    c.0
    @16
    @17
    @19
    @15
    oveq
    eqeq1d
    imbi2d
    2ralbidv
    elrab
    sylanbrc
    vx
    vy
    cA
    cB
    cD
    cR
    cN
    cX
    cY
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmul
    @2
    cD
    @24
    wceq
    @5
    cA
    cB
    cD
    cR
    vi
    vj
    vm
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatval
    adantr
    3eltr4d
end
