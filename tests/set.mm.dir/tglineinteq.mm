include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wmo.mm"
include "wceq.mm"
include "tglngne.mm"
include "tgelrnln.mm"
include "tglineneq.mm"
include "tglineintmo.mm"
include "jca.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "moi.mm"
include "syl212anc.mm"

theorem tglineinteq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglineinteq.a: |- ( ph -> A e. P )
  assume tglineinteq.b: |- ( ph -> B e. P )
  assume tglineinteq.c: |- ( ph -> C e. P )
  assume tglineinteq.d: |- ( ph -> D e. P )
  assume tglineinteq.e: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume tglineinteq.1: |- ( ph -> X e. ( A L B ) )
  assume tglineinteq.2: |- ( ph -> Y e. ( A L B ) )
  assume tglineinteq.3: |- ( ph -> X e. ( C L D ) )
  assume tglineinteq.4: |- ( ph -> Y e. ( C L D ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    cA
    cB
    cL
    co
    #
    wcel
    #
    cY
    @0
    wcel
    #
    vx
    cv
    #
    @0
    wcel
    #
    @3
    cC
    cD
    cL
    co
    #
    wcel
    #
    wa
    #
    vx
    wmo
    @1
    cX
    @5
    wcel
    #
    wa
    #
    @2
    cY
    @5
    wcel
    #
    wa
    #
    cX
    cY
    wceq
    tglineinteq.1
    tglineinteq.2
    wph
    vx
    @0
    @5
    cP
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cX
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    tglineinteq.1
    tglngne
    tgelrnln
    wph
    cP
    cG
    cI
    cL
    cC
    cD
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.c
    tglineinteq.d
    wph
    cP
    cG
    cI
    cL
    cC
    cD
    cX
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    tglineintmo.g
    tglineinteq.c
    tglineinteq.d
    tglineinteq.3
    tglngne
    tgelrnln
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    tglineinteq.c
    tglineinteq.d
    tglineinteq.e
    tglineneq
    tglineintmo
    wph
    @1
    @8
    tglineinteq.1
    tglineinteq.3
    jca
    wph
    @2
    @10
    tglineinteq.2
    tglineinteq.4
    jca
    @7
    @9
    @11
    vx
    cX
    cY
    @0
    @0
    @3
    cX
    wceq
    @4
    @1
    @6
    @8
    @3
    cX
    @0
    eleq1
    @3
    cX
    @5
    eleq1
    anbi12d
    @3
    cY
    wceq
    @4
    @2
    @6
    @10
    @3
    cY
    @0
    eleq1
    @3
    cY
    @5
    eleq1
    anbi12d
    moi
    syl212anc
end
