include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "ccnv.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem infpssrlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cN: class N
  assume infpssrlem.a: |- ( ph -> B C_ A )
  assume infpssrlem.c: |- ( ph -> F : B -1-1-onto-> A )
  assume infpssrlem.d: |- ( ph -> C e. ( A \ B ) )
  assume infpssrlem.e: |- G = ( rec ( `' F , C ) |` _om )


  assert |- ( M e. _om -> ( G ` suc M ) = ( `' F ` ( G ` M ) ) )

  proof
    cM
    com
    wcel
    cM
    csuc
    #
    cF
    ccnv
    #
    cC
    crdg
    com
    cres
    #
    cfv
    cM
    @2
    cfv
    #
    @1
    cfv
    @0
    cG
    cfv
    cM
    cG
    cfv
    #
    @1
    cfv
    cC
    cM
    @1
    frsuc
    @0
    cG
    @2
    infpssrlem.e
    fveq1i
    @4
    @3
    @1
    cM
    cG
    @2
    infpssrlem.e
    fveq1i
    fveq2i
    3eqtr4g
end
