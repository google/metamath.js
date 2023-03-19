include "wbr.mm"
include "wo.mm"
include "wcel.mm"
include "wi.mm"
include "id.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "cop.mm"
include "df-br.mm"
include "opelxp1.mm"
include "sylbi.mm"
include "3syl.mm"
include "swopolem.mm"
include "syl13anc.mm"
include "wn.mm"
include "wb.mm"
include "brdifun.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "orc.mm"
include "nsyl.mm"
include "biorf.mm"
include "syl.mm"
include "sylibrd.mm"
include "olc.mm"
include "impbid.mm"

theorem swoord1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.lt: class .<
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cY: class Y
  assume swoer.1: |- R = ( ( X X. X ) \ ( .< u. `' .< ) )
  assume swoer.2: |- ( ( ph /\ ( y e. X /\ z e. X ) ) -> ( y .< z -> -. z .< y ) )
  assume swoer.3: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x .< y -> ( x .< z \/ z .< y ) ) )
  assume swoord.4: |- ( ph -> B e. X )
  assume swoord.5: |- ( ph -> C e. X )
  assume swoord.6: |- ( ph -> A R B )

  disjoint x y
  disjoint x z
  disjoint .< x
  disjoint y z
  disjoint .< y
  disjoint .< z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint u v
  disjoint u w
  disjoint R u
  disjoint v w
  disjoint R v
  disjoint R w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint X u
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( A .< C <-> B .< C ) )

  proof
    wph
    cA
    cC
    c.lt
    wbr
    #
    cB
    cC
    c.lt
    wbr
    #
    wph
    @0
    cA
    cB
    c.lt
    wbr
    #
    @1
    wo
    #
    @1
    wph
    wph
    cA
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @0
    @3
    wi
    wph
    id
    #
    wph
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cX
    cX
    cxp
    #
    wbr
    #
    @4
    swoord.6
    cR
    @9
    cA
    cB
    cR
    @9
    c.lt
    c.lt
    ccnv
    cun
    #
    cdif
    @9
    swoer.1
    @9
    @11
    difss
    eqsstri
    ssbri
    @10
    cA
    cB
    cop
    @9
    wcel
    @4
    cA
    cB
    @9
    df-br
    cA
    cB
    cX
    cX
    opelxp1
    sylbi
    3syl
    #
    swoord.5
    swoord.4
    wph
    vx
    vy
    vz
    cX
    c.lt
    cA
    cC
    cB
    swoer.3
    swopolem
    syl13anc
    wph
    @2
    wn
    @1
    @3
    wb
    wph
    @2
    cB
    cA
    c.lt
    wbr
    #
    wo
    #
    @2
    wph
    @8
    @14
    wn
    #
    swoord.6
    wph
    @4
    @6
    @8
    @15
    wb
    @12
    swoord.4
    cA
    cB
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl2anc
    mpbid
    #
    @2
    @13
    orc
    nsyl
    @2
    @1
    biorf
    syl
    sylibrd
    wph
    @1
    @13
    @0
    wo
    #
    @0
    wph
    wph
    @6
    @5
    @4
    @1
    @17
    wi
    @7
    swoord.4
    swoord.5
    @12
    wph
    vx
    vy
    vz
    cX
    c.lt
    cB
    cC
    cA
    swoer.3
    swopolem
    syl13anc
    wph
    @13
    wn
    @0
    @17
    wb
    wph
    @14
    @13
    @16
    @13
    @2
    olc
    nsyl
    @13
    @0
    biorf
    syl
    sylibrd
    impbid
end
