include "cnrg.mm"
include "wcel.mm"
include "cdr.mm"
include "ccms.mm"
include "w3a.mm"
include "crglmod.mm"
include "cfv.mm"
include "cbn.mm"
include "cbs.mm"
include "ctopn.mm"
include "ccld.mm"
include "cress.mm"
include "co.mm"
include "cuni.mm"
include "ctps.mm"
include "wceq.mm"
include "cmt.mm"
include "simp3.mm"
include "cmsms.mm"
include "mstps.mm"
include "3syl.mm"
include "eqid.mm"
include "tpsuni.mm"
include "syl.mm"
include "ctop.mm"
include "tpstop.mm"
include "topcld.mm"
include "eqeltrd.mm"
include "ressid.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "csubrg.mm"
include "wa.mm"
include "wb.mm"
include "simp1.mm"
include "crg.mm"
include "nrgring.mm"
include "subrgid.mm"
include "rlmval.mm"
include "srabn.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem rlmbn
  let cR: class R


  assert |- ( ( R e. NrmRing /\ R e. DivRing /\ R e. CMetSp ) -> ( ringLMod ` R ) e. Ban )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cdr
    wcel
    #
    cR
    ccms
    wcel
    #
    w3a
    #
    cR
    crglmod
    cfv
    #
    cbn
    wcel
    #
    cR
    cbs
    cfv
    #
    cR
    ctopn
    cfv
    #
    ccld
    cfv
    #
    wcel
    #
    cR
    @6
    cress
    co
    #
    cdr
    wcel
    #
    @3
    @6
    @7
    cuni
    #
    @8
    @3
    cR
    ctps
    wcel
    #
    @6
    @12
    wceq
    @3
    @2
    cR
    cmt
    wcel
    @13
    @0
    @1
    @2
    simp3
    #
    cR
    cmsms
    cR
    mstps
    3syl
    #
    @6
    @7
    cR
    @6
    eqid
    #
    @7
    eqid
    #
    tpsuni
    syl
    @3
    @13
    @7
    ctop
    wcel
    @12
    @8
    wcel
    @15
    @7
    cR
    @17
    tpstop
    @7
    @12
    @12
    eqid
    topcld
    3syl
    eqeltrd
    @3
    @10
    cR
    cdr
    @0
    @1
    @10
    cR
    wceq
    @2
    @6
    cR
    cnrg
    @16
    ressid
    3ad2ant1
    @0
    @1
    @2
    simp2
    eqeltrd
    @3
    @0
    @2
    @6
    cR
    csubrg
    cfv
    wcel
    #
    @5
    @9
    @11
    wa
    wb
    @0
    @1
    @2
    simp1
    @14
    @3
    cR
    crg
    wcel
    #
    @18
    @0
    @1
    @19
    @2
    cR
    nrgring
    3ad2ant1
    @6
    cR
    @16
    subrgid
    syl
    @4
    @6
    @7
    cR
    cR
    rlmval
    @17
    srabn
    syl3anc
    mpbir2and
end
