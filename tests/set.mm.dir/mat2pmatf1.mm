include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "mat2pmatf.mm"
include "co.mm"
include "cascl.mm"
include "w3a.mm"
include "simpl.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eqid.mm"
include "mat2pmatvalel.mm"
include "sylan.mm"
include "simpr.mm"
include "eqeq12d.mm"
include "cbs.mm"
include "ply1sclf1.mm"
include "ad3antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "simplrl.mm"
include "matecld.mm"
include "simplrr.mm"
include "f1veqaeq.mm"
include "syl12anc.mm"
include "sylbid.mm"
include "ralimdvva.mm"
include "wb.mm"
include "mat2pmatbas0.mm"
include "syl.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "adantl.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem mat2pmatf1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B -1-1-> H )

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
    cB
    cH
    cT
    wf
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    cT
    cfv
    #
    wceq
    #
    @3
    @5
    wceq
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cH
    cT
    wf1
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatf
    @2
    @9
    vx
    vy
    cB
    cB
    @2
    @3
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    wa
    #
    vi
    cv
    #
    vj
    cv
    #
    @4
    co
    #
    @14
    @15
    @6
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @14
    @15
    @3
    co
    #
    @14
    @15
    @5
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @7
    @8
    @13
    @18
    @22
    vi
    vj
    cN
    cN
    @13
    @14
    cN
    wcel
    #
    @15
    cN
    wcel
    #
    wa
    #
    wa
    #
    @18
    @20
    cP
    cascl
    cfv
    #
    cfv
    #
    @21
    @28
    cfv
    #
    wceq
    #
    @22
    @27
    @16
    @29
    @17
    @30
    @13
    @0
    @1
    @10
    w3a
    #
    @26
    @16
    @29
    wceq
    @13
    @2
    @10
    wa
    @32
    @12
    @10
    @2
    @10
    @11
    simpl
    anim2i
    @0
    @1
    @10
    df-3an
    sylibr
    #
    cA
    cB
    cP
    cR
    @28
    cT
    @3
    cN
    crg
    @14
    @15
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @28
    eqid
    #
    mat2pmatvalel
    sylan
    @13
    @0
    @1
    @11
    w3a
    #
    @26
    @17
    @30
    wceq
    @13
    @2
    @11
    wa
    @35
    @12
    @11
    @2
    @10
    @11
    simpr
    anim2i
    @0
    @1
    @11
    df-3an
    sylibr
    #
    cA
    cB
    cP
    cR
    @28
    cT
    @5
    cN
    crg
    @14
    @15
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @34
    mat2pmatvalel
    sylan
    eqeq12d
    @27
    cR
    cbs
    cfv
    #
    cP
    cbs
    cfv
    #
    @28
    wf1
    #
    @20
    @37
    wcel
    @21
    @37
    wcel
    @31
    @22
    wi
    @1
    @39
    @0
    @12
    @26
    @28
    @38
    cP
    cR
    @37
    mat2pmatbas.p
    @34
    @37
    eqid
    #
    @38
    eqid
    ply1sclf1
    ad3antlr
    @27
    cA
    cB
    cR
    @14
    @15
    @37
    @3
    cN
    mat2pmatbas.a
    @40
    mat2pmatbas.b
    @13
    @24
    @25
    simprl
    #
    @13
    @24
    @25
    simprr
    #
    @2
    @10
    @11
    @26
    simplrl
    matecld
    @27
    cA
    cB
    cR
    @14
    @15
    @37
    @5
    cN
    mat2pmatbas.a
    @40
    mat2pmatbas.b
    @41
    @42
    @2
    @10
    @11
    @26
    simplrr
    matecld
    @37
    @38
    @20
    @21
    @28
    f1veqaeq
    syl12anc
    sylbid
    ralimdvva
    @13
    @4
    cH
    wcel
    #
    @6
    cH
    wcel
    #
    @7
    @19
    wb
    @13
    @32
    @43
    @33
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    @3
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatbas0
    syl
    @13
    @35
    @44
    @36
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    @5
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatbas0
    syl
    cC
    cH
    cP
    vi
    vj
    cN
    @4
    @6
    mat2pmatbas.c
    mat2pmatbas0.h
    eqmat
    syl2anc
    @12
    @8
    @23
    wb
    @2
    cA
    cB
    cR
    vi
    vj
    cN
    @3
    @5
    mat2pmatbas.a
    mat2pmatbas.b
    eqmat
    adantl
    3imtr4d
    ralrimivva
    vx
    vy
    cB
    cH
    cT
    dff13
    sylanbrc
end
