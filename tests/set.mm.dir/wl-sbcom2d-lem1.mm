include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wa.mm"
include "nfna1.mm"
include "nfeqf2.mm"
include "nfan1.mm"
include "sbequ.mm"
include "adantl.mm"
include "sbbid.mm"
include "ancoms.mm"
include "sylan9bbr.mm"
include "expr.mm"

theorem wl-sbcom2d-lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint u v
  disjoint u x
  disjoint v x
  disjoint u y
  disjoint v y
  disjoint u w
  disjoint v w
  disjoint u z
  disjoint v z
  disjoint ph u
  disjoint ph v
  assert |- ( ( u = y /\ v = w ) -> ( -. A. x x = w -> ( [ u / x ] [ v / z ] ph <-> [ y / x ] [ w / z ] ph ) ) )

  proof
    vu
    vy
    weq
    #
    vv
    vw
    weq
    #
    vx
    vw
    weq
    #
    vx
    wal
    wn
    #
    wph
    vz
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    wph
    vz
    vw
    wsb
    #
    vx
    vy
    wsb
    #
    wb
    @1
    @3
    wa
    @5
    @6
    vx
    vu
    wsb
    #
    @0
    @7
    @3
    @1
    @5
    @8
    wb
    @3
    @1
    wa
    @4
    @6
    vx
    vu
    @3
    @1
    vx
    @2
    vx
    nfna1
    vx
    vw
    vv
    nfeqf2
    nfan1
    @1
    @4
    @6
    wb
    @3
    wph
    vv
    vw
    vz
    sbequ
    adantl
    sbbid
    ancoms
    @6
    vu
    vy
    vx
    sbequ
    sylan9bbr
    expr
end
