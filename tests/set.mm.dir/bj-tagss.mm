include "bj-ctag.mm"
include "bj-csngl.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "df-bj-tag.mm"
include "bj-snglss.mm"
include "wcel.mm"
include "wss.mm"
include "0elpw.mm"
include "0ex.mm"
include "snss.mm"
include "mpbi.mm"
include "unssi.mm"
include "eqsstri.mm"

theorem bj-tagss
  let cA: class A


  assert |- tag A C_ ~P A

  proof
    cA
    bj-ctag
    cA
    bj-csngl
    #
    c0
    csn
    #
    cun
    cA
    cpw
    #
    cA
    df-bj-tag
    @0
    @1
    @2
    cA
    bj-snglss
    c0
    @2
    wcel
    @1
    @2
    wss
    cA
    0elpw
    c0
    @2
    0ex
    snss
    mpbi
    unssi
    eqsstri
end
