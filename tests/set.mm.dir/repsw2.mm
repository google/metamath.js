include "wcel.mm"
include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "c2.mm"
include "creps.mm"
include "df-s2.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "repswccat.mm"
include "mp3an23.mm"
include "repsw1.mm"
include "oveq12d.mm"
include "1p1e2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "syl5req.mm"

theorem repsw2
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( S repeatS 2 ) = <" S S "> )

  proof
    cS
    cV
    wcel
    #
    cS
    cS
    cs2
    cS
    cs1
    #
    @1
    cconcat
    co
    #
    cS
    c2
    creps
    co
    #
    cS
    cS
    df-s2
    @0
    cS
    c1
    creps
    co
    #
    @4
    cconcat
    co
    #
    cS
    c1
    c1
    caddc
    co
    #
    creps
    co
    #
    @2
    @3
    @0
    c1
    cn0
    wcel
    #
    @8
    @5
    @7
    wceq
    1nn0
    1nn0
    cS
    c1
    c1
    cV
    repswccat
    mp3an23
    @0
    @4
    @1
    @4
    @1
    cconcat
    cS
    cV
    repsw1
    #
    @9
    oveq12d
    @0
    @6
    c2
    cS
    creps
    @6
    c2
    wceq
    @0
    1p1e2
    a1i
    oveq2d
    3eqtr3d
    syl5req
end
