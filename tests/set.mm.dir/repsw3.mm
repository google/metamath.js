include "wcel.mm"
include "cs3.mm"
include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "c3.mm"
include "creps.mm"
include "df-s3.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "1nn0.mm"
include "repswccat.mm"
include "mp3an23.mm"
include "repsw2.mm"
include "repsw1.mm"
include "oveq12d.mm"
include "2p1e3.mm"
include "a1i.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "syl5req.mm"

theorem repsw3
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( S repeatS 3 ) = <" S S S "> )

  proof
    cS
    cV
    wcel
    #
    cS
    cS
    cS
    cs3
    cS
    cS
    cs2
    #
    cS
    cs1
    #
    cconcat
    co
    #
    cS
    c3
    creps
    co
    #
    cS
    cS
    cS
    df-s3
    @0
    cS
    c2
    creps
    co
    #
    cS
    c1
    creps
    co
    #
    cconcat
    co
    #
    cS
    c2
    c1
    caddc
    co
    #
    creps
    co
    #
    @3
    @4
    @0
    c2
    cn0
    wcel
    c1
    cn0
    wcel
    @7
    @9
    wceq
    2nn0
    1nn0
    cS
    c1
    c2
    cV
    repswccat
    mp3an23
    @0
    @5
    @1
    @6
    @2
    cconcat
    cS
    cV
    repsw2
    cS
    cV
    repsw1
    oveq12d
    @0
    @8
    c3
    cS
    creps
    @8
    c3
    wceq
    @0
    2p1e3
    a1i
    oveq2d
    3eqtr3d
    syl5req
end
