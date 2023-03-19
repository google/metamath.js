include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cn.mm"
include "cin.mm"
include "c0.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "simplr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "zring.mm"
include "cminusg.mm"
include "ccnfld.mm"
include "cz.mm"
include "csubg.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "clidl.mm"
include "wss.mm"
include "zringbas.mm"
include "eqid.mm"
include "lidlss.mm"
include "syl.mm"
include "sselda.mm"
include "df-zring.mm"
include "subginv.mm"
include "sylancr.mm"
include "cc.mm"
include "zcnd.mm"
include "cnfldneg.mm"
include "eqtr3d.mm"
include "crg.mm"
include "zringring.mm"
include "a1i.mm"
include "adantr.mm"
include "simpr.mm"
include "lidlnegcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "wo.mm"
include "zred.mm"
include "absord.mm"
include "mpjaod.mm"
include "nnabscl.mm"
include "sylan.mm"
include "elind.mm"
include "ne0i.mm"
include "csn.mm"
include "wrex.mm"
include "zring0.mm"
include "lidlnz.mm"
include "r19.29a.mm"

theorem zringlpirlem1
  let wph: wff ph
  let cI: class I
  let va: setvar a
  assume zringlpirlem.i: |- ( ph -> I e. ( LIdeal ` ZZring ) )
  assume zringlpirlem.n0: |- ( ph -> I =/= { 0 } )


  assert |- ( ph -> ( I i^i NN ) =/= (/) )

  proof
    wph
    va
    cv
    #
    cc0
    wne
    #
    cI
    cn
    cin
    #
    c0
    wne
    #
    va
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @1
    wa
    #
    @0
    cabs
    cfv
    #
    @2
    wcel
    @3
    @6
    cI
    cn
    @7
    @6
    @7
    @0
    wceq
    #
    @7
    cI
    wcel
    #
    @7
    @0
    cneg
    #
    wceq
    #
    @6
    @9
    @8
    @4
    wph
    @4
    @1
    simplr
    @7
    @0
    cI
    eleq1
    syl5ibrcom
    @6
    @9
    @11
    @10
    cI
    wcel
    #
    @5
    @12
    @1
    @5
    @0
    zring
    cminusg
    cfv
    #
    cfv
    #
    @10
    cI
    @5
    @0
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    @14
    @10
    @5
    cz
    ccnfld
    csubg
    cfv
    wcel
    #
    @0
    cz
    wcel
    #
    @16
    @14
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @17
    zsubrg
    cz
    ccnfld
    subrgsubg
    ax-mp
    wph
    cI
    cz
    @0
    wph
    cI
    zring
    clidl
    cfv
    #
    wcel
    #
    cI
    cz
    wss
    zringlpirlem.i
    cz
    cI
    @19
    zring
    zringbas
    @19
    eqid
    #
    lidlss
    syl
    sselda
    #
    cz
    ccnfld
    zring
    @15
    @13
    @0
    df-zring
    @15
    eqid
    @13
    eqid
    #
    subginv
    sylancr
    @5
    @0
    cc
    wcel
    @16
    @10
    wceq
    @5
    @0
    @22
    zcnd
    @0
    cnfldneg
    syl
    eqtr3d
    @5
    zring
    crg
    wcel
    #
    @20
    @4
    @14
    cI
    wcel
    @24
    @5
    zringring
    a1i
    wph
    @20
    @4
    zringlpirlem.i
    adantr
    wph
    @4
    simpr
    zring
    @19
    cI
    @13
    @0
    @21
    @23
    lidlnegcl
    syl3anc
    eqeltrrd
    adantr
    @7
    @10
    cI
    eleq1
    syl5ibrcom
    @5
    @8
    @11
    wo
    @1
    @5
    @0
    @5
    @0
    @22
    zred
    absord
    adantr
    mpjaod
    @5
    @18
    @1
    @7
    cn
    wcel
    @22
    @0
    nnabscl
    sylan
    elind
    @2
    @7
    ne0i
    syl
    wph
    @24
    @20
    cI
    cc0
    csn
    wne
    @1
    va
    cI
    wrex
    @24
    wph
    zringring
    a1i
    zringlpirlem.i
    zringlpirlem.n0
    va
    zring
    @19
    cI
    cc0
    @21
    zring0
    lidlnz
    syl3anc
    r19.29a
end
