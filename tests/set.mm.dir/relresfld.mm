include "wrel.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wi.mm"
include "relfld.mm"
include "reseq2d.mm"
include "resundi.mm"
include "wa.mm"
include "eqtr.mm"
include "wss.mm"
include "resss.mm"
include "resdm.mm"
include "ssequn2.mm"
include "uneq1.mm"
include "eqeq2d.mm"
include "ex.mm"
include "syl6bi.mm"
include "com3r.mm"
include "sylbi.mm"
include "mpsyl.mm"
include "syl5com.mm"
include "sylancl.mm"
include "pm2.43i.mm"

theorem relresfld
  let cR: class R


  assert |- ( Rel R -> ( R |` U. U. R ) = R )

  proof
    cR
    wrel
    #
    cR
    cR
    cuni
    cuni
    #
    cres
    #
    cR
    wceq
    #
    @0
    @2
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    wceq
    #
    @7
    cR
    @4
    cres
    #
    cR
    @5
    cres
    #
    cun
    #
    wceq
    #
    @0
    @3
    wi
    @0
    @1
    @6
    cR
    cR
    relfld
    reseq2d
    cR
    @4
    @5
    resundi
    @8
    @12
    wa
    @2
    @11
    wceq
    #
    @0
    @3
    @2
    @7
    @11
    eqtr
    @10
    cR
    wss
    #
    @0
    @9
    cR
    wceq
    #
    @13
    @3
    wi
    #
    cR
    @5
    resss
    cR
    resdm
    @14
    cR
    @10
    cun
    #
    cR
    wceq
    #
    @15
    @16
    wi
    @10
    cR
    ssequn2
    @15
    @13
    @18
    @3
    @15
    @13
    @2
    @17
    wceq
    #
    @18
    @3
    wi
    @15
    @11
    @17
    @2
    @9
    cR
    @10
    uneq1
    eqeq2d
    @19
    @18
    @3
    @2
    @17
    cR
    eqtr
    ex
    syl6bi
    com3r
    sylbi
    mpsyl
    syl5com
    sylancl
    pm2.43i
end
