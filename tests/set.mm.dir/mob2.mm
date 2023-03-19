include "wcel.mm"
include "wmo.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "simp3.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "wa.mm"
include "wsb.mm"
include "wal.mm"
include "nfv.mm"
include "sbhypf.mm"
include "anbi2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "nfs1v.mm"
include "sbequ12.mm"
include "mo4f.mm"
include "sp.mm"
include "sylbi.mm"
include "impel.mm"
include "expd.mm"
include "3impia.mm"
include "impbid.mm"

theorem mob2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume moi2.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint ps y
  assert |- ( ( A e. B /\ E* x ph /\ ph ) -> ( x = A <-> ps ) )

  proof
    cA
    cB
    wcel
    #
    wph
    vx
    wmo
    #
    wph
    w3a
    #
    vx
    cv
    #
    cA
    wceq
    #
    wps
    @2
    wph
    @4
    wps
    @0
    @1
    wph
    simp3
    moi2.1
    syl5ibcom
    @0
    @1
    wph
    wps
    @4
    wi
    @0
    @1
    wa
    wph
    wps
    @4
    @0
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    @3
    vy
    cv
    #
    wceq
    #
    wi
    #
    vy
    wal
    #
    wph
    wps
    wa
    #
    @4
    wi
    #
    @1
    @9
    @12
    vy
    cA
    cB
    @7
    cA
    wceq
    #
    @6
    @11
    @8
    @4
    @13
    @5
    wps
    wph
    wph
    wps
    vx
    vy
    cA
    wps
    vx
    nfv
    moi2.1
    sbhypf
    anbi2d
    @7
    cA
    @3
    eqeq2
    imbi12d
    spcgv
    @1
    @10
    vx
    wal
    @10
    wph
    @5
    vx
    vy
    wph
    vx
    vy
    nfs1v
    wph
    vx
    vy
    sbequ12
    mo4f
    @10
    vx
    sp
    sylbi
    impel
    expd
    3impia
    impbid
end
