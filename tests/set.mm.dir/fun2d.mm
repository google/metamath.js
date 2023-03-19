include "wf.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "fun2.mm"
include "syl21anc.mm"

theorem fun2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume fun2d.f: |- ( ph -> F : A --> C )
  assume fun2d.g: |- ( ph -> G : B --> C )
  assume fun2d.i: |- ( ph -> ( A i^i B ) = (/) )


  assert |- ( ph -> ( F u. G ) : ( A u. B ) --> C )

  proof
    wph
    cA
    cC
    cF
    wf
    cB
    cC
    cG
    wf
    cA
    cB
    cin
    c0
    wceq
    cA
    cB
    cun
    cC
    cF
    cG
    cun
    wf
    fun2d.f
    fun2d.g
    fun2d.i
    cA
    cB
    cC
    cF
    cG
    fun2
    syl21anc
end
