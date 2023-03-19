include "c0.mm"
include "cfv.mm"
include "ccnv.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "fr0g.mm"
include "syl.mm"
include "syl5eq.mm"

theorem infpssrlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cM: class M
  let cN: class N
  assume infpssrlem.a: |- ( ph -> B C_ A )
  assume infpssrlem.c: |- ( ph -> F : B -1-1-onto-> A )
  assume infpssrlem.d: |- ( ph -> C e. ( A \ B ) )
  assume infpssrlem.e: |- G = ( rec ( `' F , C ) |` _om )


  assert |- ( ph -> ( G ` (/) ) = C )

  proof
    wph
    c0
    cG
    cfv
    c0
    cF
    ccnv
    #
    cC
    crdg
    com
    cres
    #
    cfv
    #
    cC
    c0
    cG
    @1
    infpssrlem.e
    fveq1i
    wph
    cC
    cA
    cB
    cdif
    #
    wcel
    @2
    cC
    wceq
    infpssrlem.d
    cC
    @3
    @0
    fr0g
    syl
    syl5eq
end
