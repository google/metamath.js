include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
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
include "scmatsrng.mm"
include "sylan2.mm"
include "subrgring.mm"
include "syl.mm"
include "cif.mm"
include "cmpt2.mm"
include "w3a.mm"
include "simp1lr.mm"
include "eqid.mm"
include "simp2.mm"
include "simp3.mm"
include "scmatmat.mm"
include "imp.mm"
include "adantrr.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "adantrl.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "ifeq1d.mm"
include "mpt2eq3dva.mm"
include "cdmat.mm"
include "anim2i.mm"
include "adantr.mm"
include "wi.mm"
include "scmatdmat.mm"
include "anim12d.mm"
include "dmatmul.mm"
include "syl2anc.mm"
include "ancomd.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
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

theorem scmatcrng
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cE: class E
  let cN: class N
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  let vz: setvar z
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )
  assume scmatcrng.c: |- C = ( A |`s S )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> C e. CRing )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
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
    cS
    cA
    csubrg
    cfv
    #
    wcel
    #
    @3
    @1
    @0
    cR
    crg
    wcel
    #
    @14
    cR
    crngring
    #
    cA
    cB
    cR
    cS
    cE
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatsrng
    sylan2
    #
    cS
    cA
    cC
    scmatcrng.c
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
    cS
    wral
    #
    vx
    cS
    wral
    #
    @2
    @21
    vx
    vy
    cS
    cS
    @2
    @4
    cS
    wcel
    #
    @5
    cS
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
    @28
    @29
    @4
    co
    #
    @28
    @29
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
    @30
    @32
    @31
    @33
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    @19
    @20
    @27
    va
    vb
    cN
    cN
    @35
    @38
    @27
    @28
    cN
    wcel
    #
    @29
    cN
    wcel
    #
    w3a
    #
    @30
    @34
    @37
    c.0
    @42
    @1
    @31
    cE
    wcel
    @32
    cE
    wcel
    @34
    @37
    wceq
    @0
    @1
    @26
    @40
    @41
    simp1lr
    @42
    cA
    cA
    cbs
    cfv
    #
    cR
    @28
    @29
    cE
    @4
    cN
    scmatid.a
    scmatid.e
    @43
    eqid
    #
    @27
    @40
    @41
    simp2
    #
    @27
    @40
    @41
    simp3
    #
    @27
    @40
    @4
    @43
    wcel
    #
    @41
    @2
    @24
    @47
    @25
    @2
    @24
    @47
    cA
    @43
    cR
    cS
    @4
    cN
    ccrg
    scmatid.a
    @44
    scmatid.s
    scmatmat
    imp
    adantrr
    3ad2ant1
    matecld
    @42
    cA
    @43
    cR
    @28
    @29
    cE
    @5
    cN
    scmatid.a
    scmatid.e
    @44
    @45
    @46
    @27
    @40
    @5
    @43
    wcel
    #
    @41
    @2
    @25
    @48
    @24
    @2
    @25
    @48
    cA
    @43
    cR
    cS
    @5
    cN
    ccrg
    scmatid.a
    @44
    scmatid.s
    scmatmat
    imp
    adantrl
    3ad2ant1
    matecld
    cE
    cR
    @33
    @31
    @32
    scmatid.e
    @33
    eqid
    crngcom
    syl3anc
    ifeq1d
    mpt2eq3dva
    @27
    @0
    @15
    wa
    #
    @4
    cN
    cR
    cdmat
    co
    #
    wcel
    #
    @5
    @50
    wcel
    #
    wa
    #
    @19
    @36
    wceq
    @2
    @49
    @26
    @1
    @15
    @0
    @16
    anim2i
    adantr
    #
    @2
    @26
    @53
    @2
    @24
    @51
    @25
    @52
    @1
    @0
    @15
    @24
    @51
    wi
    @16
    cA
    cB
    @50
    cR
    cS
    cE
    @4
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    @50
    eqid
    #
    scmatdmat
    sylan2
    @1
    @0
    @15
    @25
    @52
    wi
    @16
    cA
    cB
    @50
    cR
    cS
    cE
    @5
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    @55
    scmatdmat
    sylan2
    anim12d
    imp
    #
    va
    vb
    cA
    cB
    @50
    cR
    cN
    @4
    @5
    c.0
    scmatid.a
    scmatid.b
    scmatid.0
    @55
    dmatmul
    syl2anc
    @27
    @49
    @52
    @51
    wa
    @20
    @39
    wceq
    @54
    @27
    @51
    @52
    @56
    ancomd
    va
    vb
    cA
    cB
    @50
    cR
    cN
    @5
    @4
    c.0
    scmatid.a
    scmatid.b
    scmatid.0
    @55
    dmatmul
    syl2anc
    3eqtr4d
    ralrimivva
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
    cS
    @14
    cS
    @10
    cS
    cA
    cC
    scmatcrng.c
    subrgbas
    eqcomd
    #
    @14
    @9
    @21
    vy
    @10
    cS
    @57
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
    cS
    cA
    cC
    @18
    @13
    scmatcrng.c
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
    @58
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
