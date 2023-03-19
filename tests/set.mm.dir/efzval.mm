include "cz.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "ceu.mm"
include "cmul.mm"
include "zcn.mm"
include "mulid1d.mm"
include "fveq2d.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "efexp.mm"
include "mpan.mm"
include "eqtr3d.mm"
include "df-e.mm"
include "oveq1i.mm"
include "syl6eqr.mm"

theorem efzval
  let cN: class N


  assert |- ( N e. ZZ -> ( exp ` N ) = ( _e ^ N ) )

  proof
    cN
    cz
    wcel
    #
    cN
    ce
    cfv
    #
    c1
    ce
    cfv
    #
    cN
    cexp
    co
    #
    ceu
    cN
    cexp
    co
    @0
    cN
    c1
    cmul
    co
    #
    ce
    cfv
    #
    @1
    @3
    @0
    @4
    cN
    ce
    @0
    cN
    cN
    zcn
    mulid1d
    fveq2d
    c1
    cc
    wcel
    @0
    @5
    @3
    wceq
    ax-1cn
    c1
    cN
    efexp
    mpan
    eqtr3d
    ceu
    @2
    cN
    cexp
    df-e
    oveq1i
    syl6eqr
end
