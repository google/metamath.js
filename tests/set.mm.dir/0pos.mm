include "c0.mm"
include "cpo.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "w3a.mm"
include "wral.mm"
include "0ex.mm"
include "ral0.mm"
include "base0.mm"
include "cple.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "df-ple.mm"
include "str0.mm"
include "ispos.mm"
include "mpbir2an.mm"

theorem 0pos
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- (/) e. Poset

  proof
    c0
    cpo
    wcel
    c0
    cvv
    wcel
    va
    cv
    #
    @0
    c0
    wbr
    @0
    vb
    cv
    #
    c0
    wbr
    #
    @1
    @0
    c0
    wbr
    wa
    va
    vb
    weq
    wi
    @2
    @1
    vc
    cv
    #
    c0
    wbr
    wa
    @0
    @3
    c0
    wbr
    wi
    w3a
    vc
    c0
    wral
    vb
    c0
    wral
    #
    va
    c0
    wral
    0ex
    @4
    va
    ral0
    va
    vb
    vc
    c0
    c0
    c0
    base0
    cple
    c1
    cc0
    cdc
    df-ple
    str0
    ispos
    mpbir2an
end
