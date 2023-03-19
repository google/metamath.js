include "wa.mm"
include "wss.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "simp2bi.mm"
include "adantr.mm"
include "cv.mm"
include "wcel.mm"
include "c-bnj18.mm"
include "w3a.mm"
include "cin.mm"
include "eqid.mm"
include "simp1bi.mm"
include "wbr.mm"
include "ssel2.mm"
include "syl2an.mm"
include "bnj1177.mm"
include "bnj1154.mm"
include "bnj1176.mm"
include "biid.mm"
include "bnj1175.mm"
include "bnj1174.mm"
include "bnj1173.mm"
include "bnj1172.mm"
include "bnj1171.mm"
include "bnj1186.mm"
include "bnj1185.mm"

theorem bnj1190
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vv: setvar v
  let vu: setvar u
  assume bnj1190.1: |- ( ph <-> ( R _FrSe A /\ B C_ A /\ B =/= (/) ) )
  assume bnj1190.2: |- ( ps <-> ( x e. B /\ y e. B /\ y R x ) )

  disjoint B w
  disjoint B x
  disjoint B z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint B y
  disjoint x y
  disjoint y z
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint R y
  disjoint B v
  disjoint B u
  disjoint v w
  disjoint u w
  disjoint v x
  disjoint u x
  disjoint v z
  disjoint u z
  disjoint u v
  disjoint v y
  disjoint u y
  disjoint R v
  disjoint R u
  disjoint A u
  disjoint A v
  disjoint ph u
  disjoint ph v
  disjoint ps u
  disjoint ps v
  assert |- ( ( ph /\ ps ) -> E. w e. B A. z e. B -. z R w )

  proof
    wph
    wps
    wa
    #
    vw
    vz
    vx
    vy
    cB
    cR
    @0
    vx
    vy
    vu
    vv
    cB
    cR
    wph
    wps
    vu
    vv
    cB
    cR
    wph
    wps
    vu
    vv
    cA
    cB
    cR
    wph
    cB
    cA
    wss
    #
    wps
    wph
    cA
    cR
    w-bnj15
    #
    @1
    cB
    c0
    wne
    #
    bnj1190.1
    simp2bi
    #
    adantr
    #
    wph
    wps
    @2
    vx
    cv
    #
    cA
    wcel
    #
    vu
    cv
    #
    cA
    cR
    @6
    c-bnj18
    #
    wcel
    w3a
    #
    @2
    @8
    cA
    wcel
    wa
    #
    vv
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vu
    vv
    cA
    cB
    @9
    cB
    cin
    #
    cR
    @6
    @15
    eqid
    #
    wph
    wps
    @14
    vu
    vv
    cA
    cB
    @15
    cR
    @6
    @16
    wph
    wps
    @14
    vu
    vv
    cA
    @15
    cR
    wph
    wps
    vy
    cA
    cB
    @15
    cR
    @6
    bnj1190.2
    @16
    wph
    @2
    wps
    wph
    @2
    @1
    @3
    bnj1190.1
    simp1bi
    adantr
    #
    @5
    wph
    @1
    @6
    cB
    wcel
    #
    @7
    wps
    @4
    wps
    @18
    vy
    cv
    #
    cB
    wcel
    @19
    @6
    cR
    wbr
    bnj1190.2
    simp1bi
    cB
    cA
    @6
    ssel2
    syl2an
    #
    bnj1177
    vu
    vv
    cA
    @15
    cR
    bnj1154
    bnj1176
    @10
    @11
    @13
    @12
    @8
    cR
    wbr
    wa
    w3a
    #
    @14
    vu
    vv
    cA
    cB
    @15
    cR
    @6
    @16
    @21
    biid
    @14
    biid
    #
    bnj1175
    bnj1174
    wph
    wps
    @14
    vu
    vv
    cA
    cB
    @15
    cR
    @6
    @16
    @22
    @17
    @20
    bnj1173
    bnj1172
    bnj1171
    bnj1186
    bnj1185
    bnj1185
end
