include "csu.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
include "ge0addcl.mm"
include "adantl.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "0e0icopnf.mm"
include "fsumcllem.mm"
include "simprbi.mm"
include "syl.mm"

theorem fsumge0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cM: class M
  assume fsumge0.1: |- ( ph -> A e. Fin )
  assume fsumge0.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumge0.3: |- ( ( ph /\ k e. A ) -> 0 <_ B )

  disjoint A k
  disjoint k ph
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint M k
  disjoint m ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> 0 <_ sum_ k e. A B )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wph
    vx
    vy
    cA
    cB
    @1
    vk
    @1
    cc
    wss
    wph
    @1
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    a1i
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    wa
    @4
    @5
    caddc
    co
    @1
    wcel
    wph
    @4
    @5
    ge0addcl
    adantl
    fsumge0.1
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cB
    @1
    wcel
    fsumge0.2
    fsumge0.3
    cB
    elrege0
    sylanbrc
    cc0
    @1
    wcel
    wph
    0e0icopnf
    a1i
    fsumcllem
    @2
    @0
    cr
    wcel
    @3
    @0
    elrege0
    simprbi
    syl
end
