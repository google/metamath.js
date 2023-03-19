include "wcel.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "sylanbrc.mm"

theorem eldifd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eldifd.1: |- ( ph -> A e. B )
  assume eldifd.2: |- ( ph -> -. A e. C )


  assert |- ( ph -> A e. ( B \ C ) )

  proof
    wph
    cA
    cB
    wcel
    cA
    cC
    wcel
    wn
    cA
    cB
    cC
    cdif
    wcel
    eldifd.1
    eldifd.2
    cA
    cB
    cC
    eldif
    sylanbrc
end
