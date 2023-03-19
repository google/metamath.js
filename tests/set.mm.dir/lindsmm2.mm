include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "clinds.mm"
include "cfv.mm"
include "w3a.mm"
include "cima.mm"
include "simp3.mm"
include "wss.mm"
include "wb.mm"
include "linds1.mm"
include "lindsmm.mm"
include "syl3an3.mm"
include "mpbid.mm"

theorem lindsmm2
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  let cI: class I
  assume lindfmm.b: |- B = ( Base ` S )
  assume lindfmm.c: |- C = ( Base ` T )


  assert |- ( ( G e. ( S LMHom T ) /\ G : B -1-1-> C /\ F e. ( LIndS ` S ) ) -> ( G " F ) e. ( LIndS ` T ) )

  proof
    cG
    cS
    cT
    clmhm
    co
    wcel
    #
    cB
    cC
    cG
    wf1
    #
    cF
    cS
    clinds
    cfv
    wcel
    #
    w3a
    @2
    cG
    cF
    cima
    cT
    clinds
    cfv
    wcel
    #
    @0
    @1
    @2
    simp3
    @2
    @0
    @1
    cF
    cB
    wss
    @2
    @3
    wb
    cB
    cS
    cF
    lindfmm.b
    linds1
    cB
    cC
    cS
    cT
    cF
    cG
    lindfmm.b
    lindfmm.c
    lindsmm
    syl3an3
    mpbid
end
