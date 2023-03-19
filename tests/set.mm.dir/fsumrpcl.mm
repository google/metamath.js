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
include "caddc.mm"
include "co.mm"
include "rpaddcl.mm"
include "adantl.mm"
include "fsumcl2lem.mm"

theorem fsumrpcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumcl.1: |- ( ph -> A e. Fin )
  assume fsumrpcl.2: |- ( ph -> A =/= (/) )
  assume fsumrpcl.3: |- ( ( ph /\ k e. A ) -> B e. RR+ )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sum_ k e. A B e. RR+ )

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
    caddc
    co
    crp
    wcel
    wph
    @0
    @1
    rpaddcl
    adantl
    fsumcl.1
    fsumrpcl.3
    fsumrpcl.2
    fsumcl2lem
end
