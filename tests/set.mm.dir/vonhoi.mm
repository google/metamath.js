include "cvoln.mm"
include "cfv.mm"
include "covoln.mm"
include "co.mm"
include "cv.mm"
include "cico.mm"
include "cixp.mm"
include "cdm.mm"
include "eqid.mm"
include "hoimbl.mm"
include "syl5eqel.mm"
include "mblvon.mm"
include "ovnhoi.mm"
include "eqtrd.mm"

theorem vonhoi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume vonhoi.x: |- ( ph -> X e. Fin )
  assume vonhoi.a: |- ( ph -> A : X --> RR )
  assume vonhoi.b: |- ( ph -> B : X --> RR )
  assume vonhoi.c: |- I = X_ k e. X ( ( A ` k ) [,) ( B ` k ) )
  assume vonhoi.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` I ) = ( A ( L ` X ) B ) )

  proof
    wph
    cI
    cX
    cvoln
    cfv
    #
    cfv
    cI
    cX
    covoln
    cfv
    cfv
    cA
    cB
    cX
    cL
    cfv
    co
    wph
    cI
    cX
    vonhoi.x
    wph
    cI
    vk
    cX
    vk
    cv
    #
    cA
    cfv
    @1
    cB
    cfv
    cico
    co
    cixp
    @0
    cdm
    #
    vonhoi.c
    wph
    cA
    cB
    @2
    vk
    cX
    vonhoi.x
    @2
    eqid
    vonhoi.a
    vonhoi.b
    hoimbl
    syl5eqel
    mblvon
    wph
    vx
    cA
    cB
    vk
    cI
    cL
    cX
    va
    vb
    vonhoi.x
    vonhoi.a
    vonhoi.b
    vonhoi.c
    vonhoi.l
    ovnhoi
    eqtrd
end
