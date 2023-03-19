include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "con0.mm"
include "cmps.mm"
include "eqid.mm"
include "ply1bas.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "psr1bas2.mm"
include "cps1.mm"
include "cfv.mm"
include "ressmplbas2.mm"

theorem ressply1bas2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  assume ressply1.s: |- S = ( Poly1 ` R )
  assume ressply1.h: |- H = ( R |`s T )
  assume ressply1.u: |- U = ( Poly1 ` H )
  assume ressply1.b: |- B = ( Base ` U )
  assume ressply1.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressply1bas2.w: |- W = ( PwSer1 ` H )
  assume ressply1bas2.c: |- C = ( Base ` W )
  assume ressply1bas2.k: |- K = ( Base ` S )


  assert |- ( ph -> B = ( C i^i K ) )

  proof
    wph
    cB
    cC
    cR
    c1o
    cR
    cmpl
    co
    #
    cT
    c1o
    cH
    cmpl
    co
    #
    cH
    c1o
    cK
    con0
    c1o
    cH
    cmps
    co
    #
    @0
    eqid
    ressply1.h
    @1
    eqid
    cU
    cH
    cW
    cB
    ressply1.u
    ressply1bas2.w
    ressply1.b
    ply1bas
    c1o
    con0
    wcel
    wph
    1on
    a1i
    ressply1.2
    @2
    eqid
    #
    cC
    cH
    cW
    @2
    ressply1bas2.w
    ressply1bas2.c
    @3
    psr1bas2
    cS
    cR
    cR
    cps1
    cfv
    #
    cK
    ressply1.s
    @4
    eqid
    ressply1bas2.k
    ply1bas
    ressmplbas2
end
