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
include "idd.mm"
include "wn.mm"
include "wb.mm"
include "brdifun.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "olc.mm"
include "nsyl.mm"
include "pm2.21d.mm"
include "jaod.mm"
include "syld.mm"
include "orc.mm"
include "impbid.mm"

theorem swoord2
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
  assert |- ( ph -> ( C .< A <-> C .< B ) )

  proof
    wph
    cC
    cA
    c.lt
    wbr
    #
    cC
    cB
    c.lt
    wbr
    #
    wph
    @0
    @1
    cB
    cA
    c.lt
    wbr
    #
    wo
    #
    @1
    wph
    wph
    cC
    cX
    wcel
    #
    cA
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
    swoord.5
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
    @5
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
    @5
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
    swoord.4
    wph
    vx
    vy
    vz
    cX
    c.lt
    cC
    cA
    cB
    swoer.3
    swopolem
    syl13anc
    wph
    @1
    @1
    @2
    wph
    @1
    idd
    wph
    @2
    @1
    wph
    cA
    cB
    c.lt
    wbr
    #
    @2
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
    @5
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
    olc
    nsyl
    pm2.21d
    jaod
    syld
    wph
    @1
    @0
    @13
    wo
    #
    @0
    wph
    wph
    @4
    @6
    @5
    @1
    @17
    wi
    @7
    swoord.5
    swoord.4
    @12
    wph
    vx
    vy
    vz
    cX
    c.lt
    cC
    cB
    cA
    swoer.3
    swopolem
    syl13anc
    wph
    @0
    @0
    @13
    wph
    @0
    idd
    wph
    @13
    @0
    wph
    @14
    @13
    @16
    @13
    @2
    orc
    nsyl
    pm2.21d
    jaod
    syld
    impbid
end
