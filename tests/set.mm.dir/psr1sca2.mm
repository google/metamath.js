include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "cfv.mm"
include "csca.mm"
include "wceq.mm"
include "fvi.mm"
include "psr1sca.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "c5.mm"
include "df-sca.mm"
include "str0.mm"
include "fvprc.mm"
include "cps1.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem psr1sca2
  let cP: class P
  let cR: class R
  assume psr1lmod.p: |- P = ( PwSer1 ` R )


  assert |- ( _I ` R ) = ( Scalar ` P )

  proof
    cR
    cvv
    wcel
    #
    cR
    cid
    cfv
    #
    cP
    csca
    cfv
    #
    wceq
    @0
    @1
    cR
    @2
    cR
    cvv
    fvi
    cP
    cR
    cvv
    psr1lmod.p
    psr1sca
    eqtrd
    @0
    wn
    #
    c0
    c0
    csca
    cfv
    @1
    @2
    csca
    c5
    df-sca
    str0
    cR
    cid
    fvprc
    @3
    cP
    c0
    csca
    @3
    cP
    cR
    cps1
    cfv
    c0
    psr1lmod.p
    cR
    cps1
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
