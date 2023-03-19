include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfn.mm"
include "cbs.mm"
include "cabl.mm"
include "cima.mm"
include "chash.mm"
include "cfv.mm"
include "czn.mm"
include "cen.mm"
include "wbr.mm"
include "cn0.mm"
include "ccrg.mm"
include "crg.mm"
include "hashcl.mm"
include "adantl.mm"
include "eqid.mm"
include "zncrng.mm"
include "crngring.mm"
include "ringabl.mm"
include "4syl.mm"
include "wceq.mm"
include "cn.mm"
include "hashnncl.mm"
include "biimparc.mm"
include "znhash.mm"
include "syl.mm"
include "eqcomd.mm"
include "wb.mm"
include "simpr.mm"
include "znfi.mm"
include "hashen.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "isnumbasgrplem1.mm"
include "adantll.mm"
include "wn.mm"
include "c2.mm"
include "cfrlm.mm"
include "co.mm"
include "clmod.mm"
include "2nn0.mm"
include "mp2b.mm"
include "frlmlmod.mm"
include "mpan.mm"
include "lmodabl.mm"
include "ad2antrr.mm"
include "cpw.mm"
include "cin.mm"
include "frlmpwfi.mm"
include "com.mm"
include "cdom.mm"
include "simpll.mm"
include "numinfctb.mm"
include "adantlr.mm"
include "infpwfien.mm"
include "entr.mm"
include "ensymd.mm"
include "pm2.61dan.mm"

theorem isnumbasgrplem3
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x


  assert |- ( ( S e. dom card /\ S =/= (/) ) -> S e. ( Base " Abel ) )

  proof
    cS
    ccrd
    cdm
    #
    wcel
    #
    cS
    c0
    wne
    #
    wa
    #
    cS
    cfn
    wcel
    #
    cS
    cbs
    cabl
    cima
    wcel
    #
    @2
    @4
    @5
    @1
    @2
    @4
    wa
    #
    cS
    chash
    cfv
    #
    czn
    cfv
    #
    cabl
    wcel
    #
    cS
    @8
    cbs
    cfv
    #
    cen
    wbr
    #
    @5
    @6
    @7
    cn0
    wcel
    #
    @8
    ccrg
    wcel
    @8
    crg
    wcel
    @9
    @4
    @12
    @2
    cS
    hashcl
    adantl
    @7
    @8
    @8
    eqid
    #
    zncrng
    @8
    crngring
    @8
    ringabl
    4syl
    @6
    @7
    @10
    chash
    cfv
    #
    wceq
    #
    @11
    @6
    @14
    @7
    @6
    @7
    cn
    wcel
    #
    @14
    @7
    wceq
    @4
    @16
    @2
    cS
    hashnncl
    biimparc
    #
    @10
    @7
    @8
    @13
    @10
    eqid
    #
    znhash
    syl
    eqcomd
    @6
    @4
    @10
    cfn
    wcel
    #
    @15
    @11
    wb
    @2
    @4
    simpr
    @6
    @16
    @19
    @17
    @10
    @7
    @8
    @13
    @18
    znfi
    syl
    cS
    @10
    hashen
    syl2anc
    mpbid
    @10
    cS
    @8
    @18
    isnumbasgrplem1
    syl2anc
    adantll
    @3
    @4
    wn
    #
    wa
    #
    c2
    czn
    cfv
    #
    cS
    cfrlm
    co
    #
    cabl
    wcel
    #
    cS
    @23
    cbs
    cfv
    #
    cen
    wbr
    @5
    @1
    @24
    @2
    @20
    @1
    @23
    clmod
    wcel
    #
    @24
    @22
    crg
    wcel
    #
    @1
    @26
    c2
    cn0
    wcel
    @22
    ccrg
    wcel
    @27
    2nn0
    c2
    @22
    @22
    eqid
    #
    zncrng
    @22
    crngring
    mp2b
    @22
    @23
    cS
    @0
    @23
    eqid
    #
    frlmlmod
    mpan
    @23
    lmodabl
    syl
    ad2antrr
    @21
    @25
    cS
    @21
    @25
    cS
    cpw
    cfn
    cin
    #
    cen
    wbr
    #
    @30
    cS
    cen
    wbr
    #
    @25
    cS
    cen
    wbr
    @1
    @31
    @2
    @20
    @25
    @22
    cS
    @0
    @23
    @28
    @29
    @25
    eqid
    #
    frlmpwfi
    ad2antrr
    @21
    @1
    com
    cS
    cdom
    wbr
    #
    @32
    @1
    @2
    @20
    simpll
    @1
    @20
    @34
    @2
    cS
    numinfctb
    adantlr
    cS
    infpwfien
    syl2anc
    @25
    @30
    cS
    entr
    syl2anc
    ensymd
    @25
    cS
    @23
    @33
    isnumbasgrplem1
    syl2anc
    pm2.61dan
end
