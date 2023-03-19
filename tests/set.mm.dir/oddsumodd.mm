include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "csu.mm"
include "sumodd.mm"
include "mtbid.mm"

theorem oddsumodd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume evensumodd.a: |- ( ph -> A e. Fin )
  assume evensumodd.b: |- ( ( ph /\ k e. A ) -> B e. ZZ )
  assume evensumodd.o: |- ( ( ph /\ k e. A ) -> -. 2 || B )
  assume oddsumodd.a: |- ( ph -> -. 2 || ( # ` A ) )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> -. 2 || sum_ k e. A B )

  proof
    wph
    c2
    cA
    chash
    cfv
    cdvds
    wbr
    c2
    cA
    cB
    vk
    csu
    cdvds
    wbr
    oddsumodd.a
    wph
    cA
    cB
    vk
    evensumodd.a
    evensumodd.b
    evensumodd.o
    sumodd
    mtbid
end
