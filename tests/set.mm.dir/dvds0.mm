include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "zcn.mm"
include "mul02d.mm"
include "wi.mm"
include "0z.mm"
include "w3a.mm"
include "dvds0lem.mm"
include "ex.mm"
include "mp3an13.mm"
include "mpd.mm"

theorem dvds0
  let cN: class N


  assert |- ( N e. ZZ -> N || 0 )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    cmul
    co
    cc0
    wceq
    #
    cN
    cc0
    cdvds
    wbr
    #
    @0
    cN
    cN
    zcn
    mul02d
    cc0
    cz
    wcel
    #
    @0
    @3
    @1
    @2
    wi
    0z
    0z
    @3
    @0
    @3
    w3a
    @1
    @2
    cc0
    cN
    cc0
    dvds0lem
    ex
    mp3an13
    mpd
end
