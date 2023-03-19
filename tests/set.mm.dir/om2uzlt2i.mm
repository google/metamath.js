include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "om2uzlti.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "fveq2.mm"
include "a1i.mm"
include "orim12d.mm"
include "ancoms.mm"
include "con0.mm"
include "wb.mm"
include "nnon.mm"
include "wss.mm"
include "onsseleq.mm"
include "ontri1.mm"
include "bitr3d.mm"
include "syl2anr.mm"
include "cr.mm"
include "cuz.mm"
include "om2uzuzi.mm"
include "eluzelre.mm"
include "syl.mm"
include "cle.mm"
include "leloe.mm"
include "lenlt.mm"
include "3imtr3d.mm"
include "impcon4bid.mm"

theorem om2uzlt2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- ( ( A e. _om /\ B e. _om ) -> ( A e. B <-> ( G ` A ) < ( G ` B ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cG
    cfv
    #
    cB
    cG
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    cB
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzlti
    @2
    cB
    cA
    wcel
    #
    cB
    cA
    wceq
    #
    wo
    #
    @5
    @4
    clt
    wbr
    #
    @5
    @4
    wceq
    #
    wo
    #
    @3
    wn
    #
    @6
    wn
    #
    @1
    @0
    @9
    @12
    wi
    @1
    @0
    wa
    #
    @7
    @10
    @8
    @11
    vx
    cB
    cA
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzlti
    @8
    @11
    wi
    @15
    cB
    cA
    cG
    fveq2
    a1i
    orim12d
    ancoms
    @1
    cB
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    @9
    @13
    wb
    @0
    cB
    nnon
    cA
    nnon
    @16
    @17
    wa
    cB
    cA
    wss
    @9
    @13
    cB
    cA
    onsseleq
    cB
    cA
    ontri1
    bitr3d
    syl2anr
    @1
    @5
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @12
    @14
    wb
    @0
    @1
    @5
    cC
    cuz
    cfv
    #
    wcel
    @18
    vx
    cB
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    cC
    @5
    eluzelre
    syl
    @0
    @4
    @20
    wcel
    @19
    vx
    cA
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    cC
    @4
    eluzelre
    syl
    @18
    @19
    wa
    @5
    @4
    cle
    wbr
    @12
    @14
    @5
    @4
    leloe
    @5
    @4
    lenlt
    bitr3d
    syl2anr
    3imtr3d
    impcon4bid
end
