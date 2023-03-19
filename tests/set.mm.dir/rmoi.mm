include "wrmo.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "rmob.mm"
include "biimp3ar.mm"

theorem rmoi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rmoi.b: |- ( x = B -> ( ph <-> ps ) )
  assume rmoi.c: |- ( x = C -> ( ph <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ps x
  disjoint ch x
  assert |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) /\ ( C e. A /\ ch ) ) -> B = C )

  proof
    wph
    vx
    cA
    wrmo
    cB
    cA
    wcel
    wps
    wa
    cB
    cC
    wceq
    cC
    cA
    wcel
    wch
    wa
    wph
    wps
    wch
    vx
    cA
    cB
    cC
    rmoi.b
    rmoi.c
    rmob
    biimp3ar
end
