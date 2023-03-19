include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "cc0.mm"
include "usgr1v0e.mm"
include "wb.mm"
include "oveq1.mm"
include "cn0.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "1nn0.mm"
include "2z.mm"
include "1lt2.mm"
include "olci.mm"
include "bcval4.mm"
include "mp3an.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "mpbird.mm"

theorem cusgrsizeindb1
  let cE: class E
  let cG: class G
  let cV: class V
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ ( # ` V ) = 1 ) -> ( # ` E ) = ( ( # ` V ) _C 2 ) )

  proof
    cG
    cusgr
    wcel
    #
    cV
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    cE
    chash
    cfv
    #
    @1
    c2
    cbc
    co
    #
    wceq
    #
    @3
    cc0
    wceq
    #
    cE
    cG
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    usgr1v0e
    @2
    @5
    @6
    wb
    @0
    @2
    @4
    cc0
    @3
    @2
    @4
    c1
    c2
    cbc
    co
    #
    cc0
    @1
    c1
    c2
    cbc
    oveq1
    c1
    cn0
    wcel
    c2
    cz
    wcel
    c2
    cc0
    clt
    wbr
    #
    c1
    c2
    clt
    wbr
    #
    wo
    @7
    cc0
    wceq
    1nn0
    2z
    @9
    @8
    1lt2
    olci
    c2
    c1
    bcval4
    mp3an
    syl6eq
    eqeq2d
    adantl
    mpbird
end
