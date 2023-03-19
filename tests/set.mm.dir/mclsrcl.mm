include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "cmcls.mm"
include "cfv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "0ov.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "wa.mm"
include "cv.mm"
include "cmdv.mm"
include "cpw.mm"
include "cmex.mm"
include "wi.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "fvex.mm"
include "elpw2.mm"
include "sseq2d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cmvh.mm"
include "crn.mm"
include "cun.mm"
include "cotp.mm"
include "cmax.mm"
include "cima.mm"
include "wbr.mm"
include "cmvrs.mm"
include "cxp.mm"
include "wal.mm"
include "cmsub.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "cmpt2.mm"
include "vex.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "df-mcls.mm"
include "fvmpt2.mm"
include "mp2an.mm"
include "elmpt2cl.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "simpld.mm"
include "simprd.mm"
include "3jca.mm"

theorem mclsrcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cK: class K
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vc: setvar c
  let vm: setvar m
  let vo: setvar o
  let vp: setvar p
  let vs: setvar s
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vz: setvar z
  let cH: class H
  let vy: setvar y
  let cL: class L
  let cO: class O
  let cS: class S
  let cM: class M
  let cP: class P
  let wph: wff ph
  let cQ: class Q
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )


  assert |- ( A e. ( K C B ) -> ( T e. _V /\ K C_ D /\ B C_ E ) )

  proof
    cA
    cK
    cB
    cC
    co
    #
    wcel
    #
    cT
    cvv
    wcel
    #
    cK
    cD
    wss
    #
    cB
    cE
    wss
    #
    @1
    @0
    c0
    wceq
    @2
    @0
    cA
    n0i
    @2
    wn
    #
    @0
    cK
    cB
    c0
    co
    c0
    @5
    cC
    c0
    cK
    cB
    @5
    cC
    cT
    cmcls
    cfv
    #
    c0
    mclsval.c
    cT
    cmcls
    fvprc
    syl5eq
    oveqd
    cK
    cB
    0ov
    syl6eq
    nsyl2
    #
    @1
    @3
    @4
    @2
    @1
    @3
    @4
    wa
    #
    @7
    cA
    cK
    cB
    vt
    cv
    #
    cmcls
    cfv
    #
    co
    #
    wcel
    #
    cK
    @9
    cmdv
    cfv
    #
    cpw
    #
    wcel
    #
    cB
    @9
    cmex
    cfv
    #
    cpw
    #
    wcel
    #
    wa
    #
    wi
    @1
    @8
    wi
    vt
    cT
    cvv
    @9
    cT
    wceq
    #
    @12
    @1
    @19
    @8
    @20
    @11
    @0
    cA
    @20
    @10
    cC
    cK
    cB
    @20
    @10
    @6
    cC
    @9
    cT
    cmcls
    fveq2
    mclsval.c
    syl6eqr
    oveqd
    eleq2d
    @20
    @15
    @3
    @18
    @4
    @15
    cK
    @13
    wss
    @20
    @3
    cK
    @13
    @9
    cmdv
    fvex
    #
    elpw2
    @20
    @13
    cD
    cK
    @20
    @13
    cT
    cmdv
    cfv
    cD
    @9
    cT
    cmdv
    fveq2
    mclsval.d
    syl6eqr
    sseq2d
    syl5bb
    @18
    cB
    @16
    wss
    @20
    @4
    cB
    @16
    @9
    cmex
    fvex
    #
    elpw2
    @20
    @16
    cE
    cB
    @20
    @16
    cT
    cmex
    cfv
    cE
    @9
    cT
    cmex
    fveq2
    mclsval.e
    syl6eqr
    sseq2d
    syl5bb
    anbi12d
    imbi12d
    vd
    vh
    @14
    @17
    vh
    cv
    @9
    cmvh
    cfv
    #
    crn
    #
    cun
    vc
    cv
    #
    wss
    vm
    cv
    #
    vo
    cv
    #
    vp
    cv
    #
    cotp
    @9
    cmax
    cfv
    wcel
    vs
    cv
    #
    @27
    @24
    cun
    cima
    @25
    wss
    vx
    cv
    #
    vy
    cv
    #
    @26
    wbr
    @30
    @23
    cfv
    @29
    cfv
    @9
    cmvrs
    cfv
    #
    cfv
    @31
    @23
    cfv
    @29
    cfv
    @32
    cfv
    cxp
    vd
    cv
    wss
    wi
    vy
    wal
    vx
    wal
    wa
    @28
    @29
    cfv
    @25
    wcel
    wi
    vs
    @9
    cmsub
    cfv
    crn
    wral
    wi
    vp
    wal
    vo
    wal
    vm
    wal
    wa
    vc
    cab
    cint
    #
    cK
    cB
    @10
    cA
    @9
    cvv
    wcel
    vd
    vh
    @14
    @17
    @33
    cmpt2
    #
    cvv
    wcel
    @10
    @34
    wceq
    vt
    vex
    vd
    vh
    @14
    @17
    @33
    @13
    @21
    pwex
    @16
    @22
    pwex
    mpt2ex
    vt
    cvv
    @34
    cvv
    cmcls
    vx
    vy
    vt
    vh
    vm
    vo
    vs
    vp
    vc
    vd
    df-mcls
    fvmpt2
    mp2an
    elmpt2cl
    vtoclg
    mpcom
    #
    simpld
    @1
    @3
    @4
    @35
    simprd
    3jca
end
