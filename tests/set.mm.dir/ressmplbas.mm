include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cmps.mm"
include "co.mm"
include "cin.mm"
include "eqid.mm"
include "ressmplbas2.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "ressbas2.mm"
include "syl.mm"

theorem ressmplbas
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cV: class V
  let cC: class C
  let vf: setvar f
  assume ressmpl.s: |- S = ( I mPoly R )
  assume ressmpl.h: |- H = ( R |`s T )
  assume ressmpl.u: |- U = ( I mPoly H )
  assume ressmpl.b: |- B = ( Base ` U )
  assume ressmpl.1: |- ( ph -> I e. V )
  assume ressmpl.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressmpl.p: |- P = ( S |`s B )


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
    cI
    cH
    cmps
    co
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
    cI
    @0
    cV
    @1
    ressmpl.s
    ressmpl.h
    ressmpl.u
    ressmpl.b
    ressmpl.1
    ressmpl.2
    @1
    eqid
    @2
    eqid
    @0
    eqid
    #
    ressmplbas2
    @2
    @0
    inss2
    syl6eqss
    cB
    @0
    cP
    cS
    ressmpl.p
    @3
    ressbas2
    syl
end
