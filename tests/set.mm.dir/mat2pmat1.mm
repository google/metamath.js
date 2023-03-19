include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cascl.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "3jca.mm"
include "mat2pmatvalel.mm"
include "sylan.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "fvif.mm"
include "ply1scl1.mm"
include "ad2antlr.mm"
include "ply1scl0.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "adantr.mm"
include "adantl.mm"
include "mat1ov.mm"
include "fveq2d.mm"
include "ply1ring.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "mat2pmatbas0.mm"
include "pmatring.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem mat2pmat1
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
  let vk: setvar k
  let vl: setvar l
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( T ` ( 1r ` A ) ) = ( 1r ` C ) )

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
    cA
    cur
    cfv
    #
    cT
    cfv
    #
    cC
    cur
    cfv
    #
    wceq
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
    @7
    @8
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
    @2
    @11
    vi
    vj
    cN
    cN
    @2
    @7
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    wa
    #
    wa
    #
    @9
    @7
    @8
    @3
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    @10
    @2
    @0
    @1
    @3
    cB
    wcel
    #
    w3a
    #
    @15
    @9
    @19
    wceq
    @2
    @0
    @1
    @20
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    cA
    crg
    wcel
    @20
    cA
    cR
    cN
    mat2pmatbas.a
    matring
    cB
    cA
    @3
    mat2pmatbas.b
    @3
    eqid
    #
    ringidcl
    syl
    3jca
    #
    cA
    cB
    cP
    cR
    @18
    cT
    @3
    cN
    crg
    @7
    @8
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @18
    eqid
    #
    mat2pmatvalel
    sylan
    @16
    vi
    vj
    weq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    @18
    cfv
    #
    @27
    cP
    cur
    cfv
    #
    cP
    c0g
    cfv
    #
    cif
    #
    @19
    @10
    @16
    @31
    @27
    @28
    @18
    cfv
    #
    @29
    @18
    cfv
    #
    cif
    @34
    @27
    @28
    @29
    @18
    fvif
    @16
    @27
    @35
    @32
    @36
    @33
    @1
    @35
    @32
    wceq
    @0
    @15
    @18
    cP
    cR
    @28
    @32
    mat2pmatbas.p
    @26
    @28
    eqid
    #
    @32
    eqid
    #
    ply1scl1
    ad2antlr
    @1
    @36
    @33
    wceq
    @0
    @15
    @18
    cP
    cR
    @33
    @29
    mat2pmatbas.p
    @26
    @29
    eqid
    #
    @33
    eqid
    #
    ply1scl0
    ad2antlr
    ifeq12d
    syl5eq
    @16
    @17
    @30
    @18
    @16
    cA
    cR
    @3
    @28
    @7
    @8
    cN
    @29
    mat2pmatbas.a
    @37
    @39
    @2
    @0
    @15
    @22
    adantr
    #
    @2
    @1
    @15
    @23
    adantr
    @15
    @13
    @2
    @13
    @14
    simpl
    adantl
    #
    @15
    @14
    @2
    @13
    @14
    simpr
    adantl
    #
    @24
    mat1ov
    fveq2d
    @16
    cC
    cP
    @5
    @32
    @7
    @8
    cN
    @33
    mat2pmatbas.c
    @38
    @40
    @41
    @1
    cP
    crg
    wcel
    @0
    @15
    cP
    cR
    mat2pmatbas.p
    ply1ring
    ad2antlr
    @42
    @43
    @5
    eqid
    #
    mat1ov
    3eqtr4d
    eqtrd
    ralrimivva
    @2
    @4
    cH
    wcel
    #
    @5
    cH
    wcel
    #
    @6
    @12
    wb
    @2
    @21
    @45
    @25
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
    @2
    cC
    crg
    wcel
    @46
    cC
    cP
    cR
    cN
    mat2pmatbas.p
    mat2pmatbas.c
    pmatring
    cH
    cC
    @5
    mat2pmatbas0.h
    @44
    ringidcl
    syl
    cC
    cH
    cP
    vi
    vj
    cN
    @4
    @5
    mat2pmatbas.c
    mat2pmatbas0.h
    eqmat
    syl2anc
    mpbird
end
