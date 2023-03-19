include "cabl.mm"
include "wcel.mm"
include "cclm.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cz.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "zlmlmod.mm"
include "biimpi.mm"
include "zring.mm"
include "df-zring.mm"
include "zlmsca.mm"
include "syl5reqr.mm"
include "zsubrg.mm"
include "a1i.mm"
include "eqid.mm"
include "isclmi.mm"
include "syl3anc.mm"
include "clmlmod.mm"
include "sylibr.mm"
include "impbii.mm"

theorem zlmclm
  let cG: class G
  let cW: class W
  assume zlmclm.w: |- W = ( ZMod ` G )


  assert |- ( G e. Abel <-> W e. CMod )

  proof
    cG
    cabl
    wcel
    #
    cW
    cclm
    wcel
    #
    @0
    cW
    clmod
    wcel
    #
    cW
    csca
    cfv
    #
    ccnfld
    cz
    cress
    co
    #
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    #
    @1
    @0
    @2
    cG
    cW
    zlmclm.w
    zlmlmod
    #
    biimpi
    @0
    @4
    zring
    @3
    df-zring
    cG
    cabl
    cW
    zlmclm.w
    zlmsca
    syl5reqr
    @5
    @0
    zsubrg
    a1i
    @3
    cz
    cW
    @3
    eqid
    isclmi
    syl3anc
    @1
    @2
    @0
    cW
    clmlmod
    @6
    sylibr
    impbii
end
