include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cascl.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cvv.mm"
include "simpl.mm"
include "jca.mm"
include "adantr.mm"
include "mpt2exga.mm"
include "syl.mm"
include "eqid.mm"
include "mat2pmatfval.mm"
include "mat2pmatbas0.mm"
include "3expa.mm"
include "fmpt2d.mm"

theorem mat2pmatf
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
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B --> H )

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
    vm
    vm
    cB
    vx
    vy
    cN
    cN
    vx
    cv
    vy
    cv
    vm
    cv
    #
    co
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    cH
    cT
    cvv
    @2
    @3
    cB
    wcel
    #
    wa
    @0
    @0
    wa
    #
    @6
    cvv
    wcel
    @2
    @8
    @7
    @2
    @0
    @0
    @0
    @1
    simpl
    #
    @9
    jca
    adantr
    vx
    vy
    cN
    cN
    @5
    cfn
    cfn
    mpt2exga
    syl
    vx
    vy
    cA
    cB
    cP
    cR
    @4
    cT
    vm
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @4
    eqid
    mat2pmatfval
    @0
    @1
    @7
    @3
    cT
    cfv
    cH
    wcel
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
    3expa
    fmpt2d
end
