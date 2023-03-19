include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "cfv.mm"
include "csca.mm"
include "wceq.mm"
include "fvi.mm"
include "ply1sca.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "cpl1.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "c5.mm"
include "df-sca.mm"
include "str0.mm"
include "3eqtr4g.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem ply1sca2
  let cP: class P
  let cR: class R
  assume ply1lmod.p: |- P = ( Poly1 ` R )


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
    ply1lmod.p
    ply1sca
    eqtrd
    @0
    wn
    #
    @1
    c0
    @2
    cR
    cid
    fvprc
    @3
    cR
    cpl1
    cfv
    #
    csca
    cfv
    c0
    csca
    cfv
    @2
    c0
    @3
    @4
    c0
    csca
    cR
    cpl1
    fvprc
    fveq2d
    cP
    @4
    csca
    ply1lmod.p
    fveq2i
    csca
    c5
    df-sca
    str0
    3eqtr4g
    eqtr4d
    pm2.61i
end
