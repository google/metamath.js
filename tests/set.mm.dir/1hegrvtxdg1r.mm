include "necomd.mm"
include "cpr.mm"
include "prcom.mm"
include "syl5eqss.mm"
include "1hegrvtxdg1.mm"

theorem 1hegrvtxdg1r
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


  assert |- ( ph -> ( ( VtxDeg ` G ) ` C ) = 1 )

  proof
    wph
    cA
    cC
    cB
    cE
    cG
    cV
    cX
    1hegrvtxdg1.a
    1hegrvtxdg1.c
    1hegrvtxdg1.b
    wph
    cB
    cC
    1hegrvtxdg1.n
    necomd
    1hegrvtxdg1.x
    1hegrvtxdg1.i
    wph
    cC
    cB
    cpr
    cB
    cC
    cpr
    cE
    cC
    cB
    prcom
    1hegrvtxdg1.e
    syl5eqss
    1hegrvtxdg1.v
    1hegrvtxdg1
end
