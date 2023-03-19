include "crp.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "rpmulcl.mm"
include "adantl.mm"
include "c1.mm"
include "1rp.mm"
include "fprodcllem.mm"

theorem fprodrpcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodrpcl.2: |- ( ( ph /\ k e. A ) -> B e. RR+ )

  disjoint A k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> prod_ k e. A B e. RR+ )

  proof
    wph
    vx
    vy
    cA
    cB
    crp
    vk
    crp
    cc
    wss
    wph
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    a1i
    vx
    cv
    #
    crp
    wcel
    vy
    cv
    #
    crp
    wcel
    wa
    @0
    @1
    cmul
    co
    crp
    wcel
    wph
    @0
    @1
    rpmulcl
    adantl
    fprodcl.1
    fprodrpcl.2
    c1
    crp
    wcel
    wph
    1rp
    a1i
    fprodcllem
end
