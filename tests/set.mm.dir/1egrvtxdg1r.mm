include "necomd.mm"
include "ciedg.mm"
include "cfv.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "prcom.mm"
include "a1i.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "1egrvtxdg1.mm"

theorem 1egrvtxdg1r
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume 1egrvtxdg1.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1egrvtxdg1.a: |- ( ph -> A e. X )
  assume 1egrvtxdg1.b: |- ( ph -> B e. V )
  assume 1egrvtxdg1.c: |- ( ph -> C e. V )
  assume 1egrvtxdg1.n: |- ( ph -> B =/= C )
  assume 1egrvtxdg1.i: |- ( ph -> ( iEdg ` G ) = { <. A , { B , C } >. } )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` C ) = 1 )

  proof
    wph
    cA
    cC
    cB
    cG
    cV
    cX
    1egrvtxdg1.v
    1egrvtxdg1.a
    1egrvtxdg1.c
    1egrvtxdg1.b
    wph
    cB
    cC
    1egrvtxdg1.n
    necomd
    wph
    cG
    ciedg
    cfv
    cA
    cB
    cC
    cpr
    #
    cop
    #
    csn
    cA
    cC
    cB
    cpr
    #
    cop
    #
    csn
    1egrvtxdg1.i
    wph
    @1
    @3
    wph
    @0
    @2
    cA
    @0
    @2
    wceq
    wph
    cB
    cC
    prcom
    a1i
    opeq2d
    sneqd
    eqtrd
    1egrvtxdg1
end
