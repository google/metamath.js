include "cv.mm"
include "cfv.mm"
include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "ioorrnopnxr.mm"
include "opnvonmbl.mm"

theorem ioovonmbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ioovonmbl.x: |- ( ph -> X e. Fin )
  assume ioovonmbl.s: |- S = dom ( voln ` X )
  assume ioovonmbl.a: |- ( ph -> A : X --> RR* )
  assume ioovonmbl.b: |- ( ph -> B : X --> RR* )

  disjoint A i
  disjoint B i
  disjoint X i
  disjoint i ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) e. S )

  proof
    wph
    cS
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    @0
    cB
    cfv
    cioo
    co
    cixp
    cX
    ioovonmbl.x
    ioovonmbl.s
    wph
    cA
    cB
    vi
    cX
    ioovonmbl.x
    ioovonmbl.a
    ioovonmbl.b
    ioorrnopnxr
    opnvonmbl
end
