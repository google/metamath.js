include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "tglnpt.mm"
include "perpln2.mm"
include "tglnne.mm"
include "wne.mm"
include "wcel.mm"
include "wo.mm"
include "wbr.mm"
include "w3a.mm"
include "cstrkg.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp2d.mm"
include "hlln.mm"
include "lnrot1.mm"
include "tglineelsb2.mm"
include "perpcom.mm"
include "eqbrtrrd.mm"
include "footne.mm"

theorem hlperpnel
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cU: class U
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume hlperpnel.a: |- ( ph -> A e. ran L )
  assume hlperpnel.k: |- K = ( hlG ` G )
  assume hlperpnel.1: |- ( ph -> U e. A )
  assume hlperpnel.2: |- ( ph -> V e. P )
  assume hlperpnel.3: |- ( ph -> W e. P )
  assume hlperpnel.4: |- ( ph -> A ( perpG ` G ) ( U L V ) )
  assume hlperpnel.5: |- ( ph -> V ( K ` U ) W )


  assert |- ( ph -> -. W e. A )

  proof
    wph
    cA
    cP
    cG
    cI
    cL
    c.mi
    cU
    cW
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpex.g
    hlperpnel.a
    hlperpnel.1
    hlperpnel.3
    wph
    cU
    cV
    cL
    co
    #
    cU
    cW
    cL
    co
    cA
    cG
    cperpg
    cfv
    wph
    cP
    cU
    cV
    cW
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    wph
    cA
    cP
    cG
    cI
    cL
    cU
    colperpex.p
    colperpex.l
    colperpex.i
    colperpex.g
    hlperpnel.a
    hlperpnel.1
    tglnpt
    #
    hlperpnel.2
    wph
    cP
    cG
    cI
    cL
    cU
    cV
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    @1
    hlperpnel.2
    wph
    cA
    @0
    cG
    cL
    colperpex.l
    colperpex.g
    hlperpnel.4
    perpln2
    #
    tglnne
    #
    hlperpnel.3
    wph
    cV
    cU
    wne
    #
    cW
    cU
    wne
    #
    cV
    cU
    cW
    cI
    co
    wcel
    cW
    cU
    cV
    cI
    co
    wcel
    wo
    #
    wph
    cV
    cW
    cU
    cK
    cfv
    wbr
    @4
    @5
    @6
    w3a
    hlperpnel.5
    wph
    cV
    cW
    cU
    cP
    cG
    cI
    cK
    cstrkg
    colperpex.p
    colperpex.i
    hlperpnel.k
    hlperpnel.2
    hlperpnel.3
    @1
    colperpex.g
    ishlg
    mpbid
    simp2d
    #
    wph
    cP
    cG
    cI
    cL
    cU
    cV
    cW
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    @1
    hlperpnel.2
    hlperpnel.3
    @3
    wph
    cV
    cW
    cU
    cP
    cG
    cI
    cK
    cL
    colperpex.p
    colperpex.i
    hlperpnel.k
    hlperpnel.2
    hlperpnel.3
    @1
    colperpex.g
    colperpex.l
    hlperpnel.5
    hlln
    @7
    lnrot1
    tglineelsb2
    wph
    cA
    @0
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpex.g
    hlperpnel.a
    @2
    hlperpnel.4
    perpcom
    eqbrtrrd
    footne
end
