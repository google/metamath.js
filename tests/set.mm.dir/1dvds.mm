include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "zcn.mm"
include "mulid1d.mm"
include "1z.mm"
include "dvds0lem.mm"
include "mp3anl2.mm"
include "anabsan.mm"
include "mpdan.mm"

theorem 1dvds
  let cN: class N


  assert |- ( N e. ZZ -> 1 || N )

  proof
    cN
    cz
    wcel
    #
    cN
    c1
    cmul
    co
    cN
    wceq
    #
    c1
    cN
    cdvds
    wbr
    #
    @0
    cN
    cN
    zcn
    mulid1d
    @0
    @1
    @2
    @0
    c1
    cz
    wcel
    @0
    @1
    @2
    1z
    cN
    c1
    cN
    dvds0lem
    mp3anl2
    anabsan
    mpdan
end
