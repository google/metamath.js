include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cps1.mm"
include "cin.mm"
include "eqid.mm"
include "ressply1bas2.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "ressbas2.mm"
include "syl.mm"

theorem ressply1bas
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  assume ressply1.s: |- S = ( Poly1 ` R )
  assume ressply1.h: |- H = ( R |`s T )
  assume ressply1.u: |- U = ( Poly1 ` H )
  assume ressply1.b: |- B = ( Base ` U )
  assume ressply1.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressply1.p: |- P = ( S |`s B )


  assert |- ( ph -> B = ( Base ` P ) )

  proof
    wph
    cB
    cS
    cbs
    cfv
    #
    wss
    cB
    cP
    cbs
    cfv
    wceq
    wph
    cB
    cH
    cps1
    cfv
    #
    cbs
    cfv
    #
    @0
    cin
    @0
    wph
    cB
    @2
    cR
    cS
    cT
    cU
    cH
    @0
    @1
    ressply1.s
    ressply1.h
    ressply1.u
    ressply1.b
    ressply1.2
    @1
    eqid
    @2
    eqid
    @0
    eqid
    #
    ressply1bas2
    @2
    @0
    inss2
    syl6eqss
    cB
    @0
    cP
    cS
    ressply1.p
    @3
    ressbas2
    syl
end
