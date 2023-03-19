include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "r19.26.mm"
include "wex.mm"
include "wal.mm"
include "n0.mm"
include "biimpi.mm"
include "ne0i.mm"
include "necon2bi.mm"
include "imim2i.mm"
include "ralimi.mm"
include "alrimiv.mm"
include "19.29r.mm"
include "df-rex.mm"
include "sylibr.mm"
include "syl2an.mm"
include "sylbir.mm"

theorem kmlem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let vu: setvar u
  let vy: setvar y
  let wps: wff ps

  disjoint A v
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v y
  disjoint x y
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint w y
  disjoint y z
  assert |- ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( ph -> A = (/) ) ) -> A. z e. x E. v e. z A. w e. x ( ph -> -. v e. A ) )

  proof
    vz
    cv
    #
    c0
    wne
    #
    vz
    vx
    cv
    #
    wral
    wph
    cA
    c0
    wceq
    #
    wi
    #
    vw
    @2
    wral
    #
    vz
    @2
    wral
    wa
    @1
    @5
    wa
    #
    vz
    @2
    wral
    wph
    vv
    cv
    #
    cA
    wcel
    #
    wn
    #
    wi
    #
    vw
    @2
    wral
    #
    vv
    @0
    wrex
    #
    vz
    @2
    wral
    @1
    @5
    vz
    @2
    r19.26
    @6
    @12
    vz
    @2
    @1
    @7
    @0
    wcel
    #
    vv
    wex
    #
    @11
    vv
    wal
    #
    @12
    @5
    @1
    @14
    vv
    @0
    n0
    biimpi
    @5
    @11
    vv
    @4
    @10
    vw
    @2
    @3
    @9
    wph
    @8
    cA
    c0
    cA
    @7
    ne0i
    necon2bi
    imim2i
    ralimi
    alrimiv
    @14
    @15
    wa
    @13
    @11
    wa
    vv
    wex
    @12
    @13
    @11
    vv
    19.29r
    @11
    vv
    @0
    df-rex
    sylibr
    syl2an
    ralimi
    sylbir
end
