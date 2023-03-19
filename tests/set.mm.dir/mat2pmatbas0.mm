include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cbs.mm"
include "mat2pmatbas.mm"
include "syl6eleqr.mm"

theorem mat2pmatbas0
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( T ` M ) e. H )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    cM
    cB
    wcel
    w3a
    cM
    cT
    cfv
    cC
    cbs
    cfv
    cH
    cA
    cB
    cC
    cP
    cR
    cT
    cM
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas
    mat2pmatbas0.h
    syl6eleqr
end
