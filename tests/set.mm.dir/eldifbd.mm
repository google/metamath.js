include "wcel.mm"
include "wn.mm"
include "cdif.mm"
include "wa.mm"
include "eldif.mm"
include "sylib.mm"
include "simprd.mm"

theorem eldifbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eldifbd.1: |- ( ph -> A e. ( B \ C ) )


  assert |- ( ph -> -. A e. C )

  proof
    wph
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    wn
    #
    wph
    cA
    cB
    cC
    cdif
    wcel
    @0
    @1
    wa
    eldifbd.1
    cA
    cB
    cC
    eldif
    sylib
    simprd
end
