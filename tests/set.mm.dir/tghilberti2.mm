include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "wrmo.mm"
include "w3a.mm"
include "co.mm"
include "cstrkg.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "tglinethru.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "ralrimivva.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem tghilberti2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )

  disjoint B x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint Q x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint G y
  disjoint I y
  disjoint L y
  disjoint P y
  disjoint Q y
  disjoint ph y
  assert |- ( ph -> E* x e. ran L ( P e. x /\ Q e. x ) )

  proof
    wph
    cP
    vx
    cv
    #
    wcel
    #
    cQ
    @0
    wcel
    #
    wa
    #
    cP
    vy
    cv
    #
    wcel
    #
    cQ
    @4
    wcel
    #
    wa
    #
    wa
    #
    @0
    @4
    wceq
    #
    wi
    #
    vy
    cL
    crn
    #
    wral
    vx
    @11
    wral
    @3
    vx
    @11
    wrmo
    wph
    @10
    vx
    vy
    @11
    @11
    wph
    @0
    @11
    wcel
    #
    @4
    @11
    wcel
    #
    wa
    #
    @8
    @9
    wph
    @14
    @8
    w3a
    #
    @0
    cP
    cQ
    cL
    co
    @4
    @15
    @0
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    @14
    cG
    cstrkg
    wcel
    @8
    tglineelsb2.g
    3ad2ant1
    #
    wph
    @14
    cP
    cB
    wcel
    @8
    tglineelsb2.1
    3ad2ant1
    #
    wph
    @14
    cQ
    cB
    wcel
    @8
    tglineelsb2.2
    3ad2ant1
    #
    wph
    @14
    cP
    cQ
    wne
    @8
    tglineelsb2.4
    3ad2ant1
    #
    @19
    wph
    @12
    @13
    @8
    simp2l
    @1
    @2
    @7
    wph
    @14
    simp3ll
    @1
    @2
    @7
    wph
    @14
    simp3lr
    tglinethru
    @15
    @4
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @16
    @17
    @18
    @19
    @19
    wph
    @12
    @13
    @8
    simp2r
    @5
    @6
    @3
    wph
    @14
    simp3rl
    @5
    @6
    @3
    wph
    @14
    simp3rr
    tglinethru
    eqtr4d
    3expia
    ralrimivva
    @3
    @7
    vx
    vy
    @11
    @9
    @1
    @5
    @2
    @6
    @0
    @4
    cP
    eleq2
    @0
    @4
    cQ
    eleq2
    anbi12d
    rmo4
    sylibr
end
