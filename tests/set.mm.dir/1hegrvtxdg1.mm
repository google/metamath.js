include "cpr.mm"
include "wcel.mm"
include "prid1g.mm"
include "syl.mm"
include "sseldd.mm"
include "cpw.mm"
include "prid2g.mm"
include "nehash2.mm"
include "1hevtxdg1.mm"

theorem 1hegrvtxdg1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  assume 1hegrvtxdg1.a: |- ( ph -> A e. X )
  assume 1hegrvtxdg1.b: |- ( ph -> B e. V )
  assume 1hegrvtxdg1.c: |- ( ph -> C e. V )
  assume 1hegrvtxdg1.n: |- ( ph -> B =/= C )
  assume 1hegrvtxdg1.x: |- ( ph -> E e. ~P V )
  assume 1hegrvtxdg1.i: |- ( ph -> ( iEdg ` G ) = { <. A , E >. } )
  assume 1hegrvtxdg1.e: |- ( ph -> { B , C } C_ E )
  assume 1hegrvtxdg1.v: |- ( ph -> ( Vtx ` G ) = V )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` B ) = 1 )

  proof
    wph
    cA
    cB
    cE
    cG
    cV
    cX
    1hegrvtxdg1.i
    1hegrvtxdg1.v
    1hegrvtxdg1.a
    1hegrvtxdg1.b
    1hegrvtxdg1.x
    wph
    cB
    cC
    cpr
    #
    cE
    cB
    1hegrvtxdg1.e
    wph
    cB
    cV
    wcel
    cB
    @0
    wcel
    1hegrvtxdg1.b
    cB
    cC
    cV
    prid1g
    syl
    sseldd
    #
    wph
    cB
    cC
    cE
    cV
    cpw
    1hegrvtxdg1.x
    @1
    wph
    @0
    cE
    cC
    1hegrvtxdg1.e
    wph
    cC
    cV
    wcel
    cC
    @0
    wcel
    1hegrvtxdg1.c
    cB
    cC
    cV
    prid2g
    syl
    sseldd
    1hegrvtxdg1.n
    nehash2
    1hevtxdg1
end
