include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "perpln1.mm"
include "tglnne.mm"
include "tglinerflx1.mm"
include "wceq.mm"
include "wn.mm"
include "wcel.mm"
include "neneqd.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "tglinethru.mm"
include "eqbrtrrd.mm"

theorem colperp
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
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume colperp.a: |- ( ph -> A e. P )
  assume colperp.b: |- ( ph -> B e. P )
  assume colperp.c: |- ( ph -> C e. P )
  assume colperp.1: |- ( ph -> ( A L B ) ( perpG ` G ) D )
  assume colperp.2: |- ( ph -> ( C e. ( A L B ) \/ A = B ) )
  assume colperp.3: |- ( ph -> A =/= C )


  assert |- ( ph -> ( A L C ) ( perpG ` G ) D )

  proof
    wph
    cA
    cB
    cL
    co
    #
    cA
    cC
    cL
    co
    cD
    cG
    cperpg
    cfv
    wph
    @0
    cP
    cA
    cC
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    colperp.a
    colperp.c
    colperp.3
    colperp.3
    wph
    @0
    cD
    cG
    cL
    colperpex.l
    colperpex.g
    colperp.1
    perpln1
    #
    wph
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    colperp.a
    colperp.b
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    colperp.a
    colperp.b
    @1
    tglnne
    #
    tglinerflx1
    wph
    cA
    cB
    wceq
    #
    wn
    cC
    @0
    wcel
    #
    wph
    cA
    cB
    @2
    neneqd
    wph
    @3
    @4
    wph
    @4
    @3
    colperp.2
    orcomd
    ord
    mpd
    tglinethru
    colperp.1
    eqbrtrrd
end
