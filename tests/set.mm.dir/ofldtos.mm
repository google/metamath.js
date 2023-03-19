include "cofld.mm"
include "wcel.mm"
include "comnd.mm"
include "ctos.mm"
include "corng.mm"
include "cogrp.mm"
include "cfield.mm"
include "isofld.mm"
include "simprbi.mm"
include "orngogrp.mm"
include "cgrp.mm"
include "isogrp.mm"
include "3syl.mm"
include "omndtos.mm"
include "syl.mm"

theorem ofldtos
  let cF: class F


  assert |- ( F e. oField -> F e. Toset )

  proof
    cF
    cofld
    wcel
    #
    cF
    comnd
    wcel
    #
    cF
    ctos
    wcel
    @0
    cF
    corng
    wcel
    #
    cF
    cogrp
    wcel
    #
    @1
    @0
    cF
    cfield
    wcel
    @2
    cF
    isofld
    simprbi
    cF
    orngogrp
    @3
    cF
    cgrp
    wcel
    @1
    cF
    isogrp
    simprbi
    3syl
    cF
    omndtos
    syl
end
