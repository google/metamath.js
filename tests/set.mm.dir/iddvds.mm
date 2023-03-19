include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "zcn.mm"
include "mulid2d.mm"
include "1z.mm"
include "dvds0lem.mm"
include "mp3anl1.mm"
include "anabsan.mm"
include "mpdan.mm"

theorem iddvds
  let cN: class N


  assert |- ( N e. ZZ -> N || N )

  proof
    cN
    cz
    wcel
    #
    c1
    cN
    cmul
    co
    cN
    wceq
    #
    cN
    cN
    cdvds
    wbr
    #
    @0
    cN
    cN
    zcn
    mulid2d
    @0
    @1
    @2
    c1
    cz
    wcel
    @0
    @0
    @1
    @2
    1z
    c1
    cN
    cN
    dvds0lem
    mp3anl1
    anabsan
    mpdan
end
