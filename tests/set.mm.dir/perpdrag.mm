include "cv.mm"
include "wne.mm"
include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "co.mm"
include "cperpg.mm"
include "wbr.mm"
include "perpln1.mm"
include "tglnpt.mm"
include "simplr.mm"
include "simpr.mm"
include "tglinethru.mm"
include "eleqtrd.mm"
include "eqbrtrrd.mm"
include "perprag.mm"
include "tglnpt2.mm"
include "r19.29a.mm"

theorem perpdrag
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vx: setvar x
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume perpdrag.1: |- ( ph -> A e. D )
  assume perpdrag.2: |- ( ph -> B e. D )
  assume perpdrag.3: |- ( ph -> C e. P )
  assume perpdrag.4: |- ( ph -> D ( perpG ` G ) ( B L C ) )


  assert |- ( ph -> <" A B C "> e. ( raG ` G ) )

  proof
    wph
    cA
    vx
    cv
    #
    wne
    #
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    wcel
    vx
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @1
    wa
    #
    cA
    @0
    cB
    cC
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    cG
    cstrkg
    wcel
    @2
    @1
    colperpex.g
    ad2antrr
    #
    @4
    cD
    cP
    cG
    cI
    cL
    cA
    colperpex.p
    colperpex.l
    colperpex.i
    @5
    @4
    cD
    cB
    cC
    cL
    co
    #
    cG
    cL
    colperpex.l
    @5
    wph
    cD
    @6
    cG
    cperpg
    cfv
    #
    wbr
    @2
    @1
    perpdrag.4
    ad2antrr
    #
    perpln1
    #
    wph
    cA
    cD
    wcel
    @2
    @1
    perpdrag.1
    ad2antrr
    #
    tglnpt
    #
    @4
    cD
    cP
    cG
    cI
    cL
    @0
    colperpex.p
    colperpex.l
    colperpex.i
    @5
    @9
    wph
    @2
    @1
    simplr
    #
    tglnpt
    #
    @4
    cB
    cD
    cA
    @0
    cL
    co
    #
    wph
    cB
    cD
    wcel
    @2
    @1
    perpdrag.2
    ad2antrr
    @4
    cD
    cP
    cA
    @0
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @5
    @11
    @13
    @3
    @1
    simpr
    #
    @15
    @9
    @10
    @12
    tglinethru
    #
    eleqtrd
    wph
    cC
    cP
    wcel
    @2
    @1
    perpdrag.3
    ad2antrr
    @4
    cD
    @14
    @6
    @7
    @16
    @8
    eqbrtrrd
    perprag
    wph
    vx
    cD
    cP
    cG
    cI
    cL
    cA
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    wph
    cD
    @6
    cG
    cL
    colperpex.l
    colperpex.g
    perpdrag.4
    perpln1
    perpdrag.1
    tglnpt2
    r19.29a
end
