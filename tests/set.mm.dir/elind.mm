include "wcel.mm"
include "cin.mm"
include "elin.mm"
include "sylanbrc.mm"

theorem elind
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  assume elind.1: |- ( ph -> X e. A )
  assume elind.2: |- ( ph -> X e. B )


  assert |- ( ph -> X e. ( A i^i B ) )

  proof
    wph
    cX
    cA
    wcel
    cX
    cB
    wcel
    cX
    cA
    cB
    cin
    wcel
    elind.1
    elind.2
    cX
    cA
    cB
    elin
    sylanbrc
end
