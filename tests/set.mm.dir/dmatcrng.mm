include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "crg.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "csubrg.mm"
include "crngring.mm"
include "dmatsrng.mm"
include "sylan.mm"
include "subrgring.mm"
include "syl.mm"
include "cif.mm"
include "cmpt2.mm"
include "w3a.mm"
include "simp1lr.mm"
include "eqid.mm"
include "simp2.mm"
include "simp3.mm"
include "dmatmat.mm"
include "imp.mm"
include "adantrr.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "adantrl.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "ifeq1d.mm"
include "mpt2eq3dva.mm"
include "anim2i.mm"
include "dmatmul.mm"
include "pm3.22.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ancoms.mm"
include "wb.mm"
include "subrgbas.mm"
include "eqcomd.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "mpbird.mm"
include "iscrng2.mm"
include "sylanbrc.mm"

theorem dmatcrng
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let vz: setvar z
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )
  assume dmatcrng.c: |- C = ( A |`s D )


  assert |- ( ( R e. CRing /\ N e. Fin ) -> C e. CRing )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cC
    crg
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cC
    cmulr
    cfv
    #
    co
    #
    @5
    @4
    @6
    co
    #
    wceq
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    #
    vx
    @10
    wral
    #
    cC
    ccrg
    wcel
    @2
    cD
    cA
    csubrg
    cfv
    #
    wcel
    #
    @3
    @0
    cR
    crg
    wcel
    #
    @1
    @14
    cR
    crngring
    #
    cA
    cB
    cD
    cR
    cN
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatsrng
    sylan
    #
    cD
    cA
    cC
    dmatcrng.c
    subrgring
    syl
    @2
    @12
    @4
    @5
    cA
    cmulr
    cfv
    #
    co
    #
    @5
    @4
    @18
    co
    #
    wceq
    #
    vy
    cD
    wral
    #
    vx
    cD
    wral
    #
    @1
    @0
    @23
    @1
    @0
    wa
    #
    @21
    vx
    vy
    cD
    cD
    @24
    @4
    cD
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    wa
    #
    va
    vb
    cN
    cN
    va
    cv
    #
    vb
    cv
    #
    wceq
    #
    @29
    @30
    @4
    co
    #
    @29
    @30
    @5
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
    va
    vb
    cN
    cN
    @31
    @33
    @32
    @34
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    @19
    @20
    @28
    va
    vb
    cN
    cN
    @36
    @39
    @28
    @29
    cN
    wcel
    #
    @30
    cN
    wcel
    #
    w3a
    #
    @31
    @35
    @38
    c.0
    @43
    @0
    @32
    cR
    cbs
    cfv
    #
    wcel
    @33
    @44
    wcel
    @35
    @38
    wceq
    @1
    @0
    @27
    @41
    @42
    simp1lr
    @43
    cA
    cA
    cbs
    cfv
    #
    cR
    @29
    @30
    @44
    @4
    cN
    dmatid.a
    @44
    eqid
    #
    @45
    eqid
    #
    @28
    @41
    @42
    simp2
    #
    @28
    @41
    @42
    simp3
    #
    @28
    @41
    @4
    @45
    wcel
    #
    @42
    @24
    @25
    @50
    @26
    @24
    @25
    @50
    cA
    @45
    cD
    cR
    @4
    cN
    ccrg
    c.0
    dmatid.a
    @47
    dmatid.0
    dmatid.d
    dmatmat
    imp
    adantrr
    3ad2ant1
    matecld
    @43
    cA
    @45
    cR
    @29
    @30
    @44
    @5
    cN
    dmatid.a
    @46
    @47
    @48
    @49
    @28
    @41
    @5
    @45
    wcel
    #
    @42
    @24
    @26
    @51
    @25
    @24
    @26
    @51
    cA
    @45
    cD
    cR
    @5
    cN
    ccrg
    c.0
    dmatid.a
    @47
    dmatid.0
    dmatid.d
    dmatmat
    imp
    adantrl
    3ad2ant1
    matecld
    @44
    cR
    @34
    @32
    @33
    @46
    @34
    eqid
    crngcom
    syl3anc
    ifeq1d
    mpt2eq3dva
    @24
    @1
    @15
    wa
    #
    @27
    @19
    @37
    wceq
    @0
    @15
    @1
    @16
    anim2i
    #
    va
    vb
    cA
    cB
    cD
    cR
    cN
    @4
    @5
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmul
    sylan
    @24
    @52
    @26
    @25
    wa
    @20
    @40
    wceq
    @27
    @53
    @25
    @26
    pm3.22
    va
    vb
    cA
    cB
    cD
    cR
    cN
    @5
    @4
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmul
    syl2an
    3eqtr4d
    ralrimivva
    ancoms
    @2
    @14
    @12
    @23
    wb
    @17
    @14
    @11
    @22
    vx
    @10
    cD
    @14
    cD
    @10
    cD
    cA
    cC
    dmatcrng.c
    subrgbas
    eqcomd
    #
    @14
    @9
    @21
    vy
    @10
    cD
    @54
    @14
    @7
    @19
    @8
    @20
    @14
    @6
    @18
    @4
    @5
    @14
    @18
    @6
    cD
    cA
    cC
    @18
    @13
    dmatcrng.c
    @18
    eqid
    ressmulr
    eqcomd
    #
    oveqd
    @14
    @6
    @18
    @5
    @4
    @55
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    syl
    mpbird
    vx
    vy
    @10
    cC
    @6
    @10
    eqid
    @6
    eqid
    iscrng2
    sylanbrc
end
