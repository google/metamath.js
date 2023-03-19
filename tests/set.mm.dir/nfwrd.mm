include "cword.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "df-word.mm"
include "nfcv.mm"
include "nff.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfwrd
  let vx: setvar x
  let cS: class S
  let vl: setvar l
  let vw: setvar w
  assume nfwrd.1: |- F/_ x S


  assert |- F/_ x Word S

  proof
    vx
    cS
    cword
    cc0
    vl
    cv
    cfzo
    co
    #
    cS
    vw
    cv
    #
    wf
    #
    vl
    cn0
    wrex
    #
    vw
    cab
    vw
    cS
    vl
    df-word
    @3
    vx
    vw
    @2
    vx
    vl
    cn0
    vx
    cn0
    nfcv
    vx
    @0
    cS
    @1
    vx
    @1
    nfcv
    vx
    @0
    nfcv
    nfwrd.1
    nff
    nfrex
    nfab
    nfcxfr
end
