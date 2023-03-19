include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cmul.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnred.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "simpr.mm"
include "rpregt0d.mm"
include "adantr.mm"
include "simpld.mm"
include "rpge0d.mm"
include "wb.mm"
include "rpred.mm"
include "fznnfl.mm"
include "syl.mm"
include "simplbda.mm"
include "lemul2ad.mm"
include "wceq.mm"
include "cc.mm"
include "rpcn.mm"
include "sqvald.mm"
include "breqtrrd.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "nnrpd.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "nndivre.mm"
include "syl2an.mm"
include "flword2.mm"
include "syl3anc.mm"
include "jca.mm"

theorem dchrisum0lem1a
  let wph: wff ph
  let cD: class D
  let cX: class X


  assert |- ( ( ( ph /\ X e. RR+ ) /\ D e. ( 1 ... ( |_ ` X ) ) ) -> ( X <_ ( ( X ^ 2 ) / D ) /\ ( |_ ` ( ( X ^ 2 ) / D ) ) e. ( ZZ>= ` ( |_ ` X ) ) ) )

  proof
    wph
    cX
    crp
    wcel
    #
    wa
    #
    cD
    c1
    cX
    cfl
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cX
    cX
    c2
    cexp
    co
    #
    cD
    cdiv
    co
    #
    cle
    wbr
    #
    @6
    cfl
    cfv
    @2
    cuz
    cfv
    wcel
    #
    @4
    cX
    cD
    cmul
    co
    #
    @5
    cle
    wbr
    @7
    @4
    @9
    cX
    cX
    cmul
    co
    #
    @5
    cle
    @4
    cD
    cX
    cX
    @4
    cD
    @3
    cD
    cn
    wcel
    #
    @1
    cD
    @2
    elfznn
    #
    adantl
    #
    nnred
    @4
    cX
    cr
    wcel
    #
    cc0
    cX
    clt
    wbr
    #
    @1
    @14
    @15
    wa
    @3
    @1
    cX
    wph
    @0
    simpr
    #
    rpregt0d
    adantr
    simpld
    #
    @17
    @4
    cX
    @1
    @0
    @3
    @16
    adantr
    rpge0d
    @1
    @3
    @11
    cD
    cX
    cle
    wbr
    #
    @1
    @14
    @3
    @11
    @18
    wa
    wb
    @1
    cX
    @16
    rpred
    cD
    cX
    fznnfl
    syl
    simplbda
    lemul2ad
    @1
    @5
    @10
    wceq
    @3
    @1
    cX
    @0
    cX
    cc
    wcel
    wph
    cX
    rpcn
    adantl
    sqvald
    adantr
    breqtrrd
    @4
    cX
    @5
    cD
    @17
    @1
    @5
    cr
    wcel
    #
    @3
    @1
    @5
    @1
    @0
    c2
    cz
    wcel
    @5
    crp
    wcel
    @16
    2z
    cX
    c2
    rpexpcl
    sylancl
    rpred
    #
    adantr
    @4
    cD
    @13
    nnrpd
    lemuldivd
    mpbid
    #
    @4
    @14
    @6
    cr
    wcel
    #
    @7
    @8
    @17
    @1
    @19
    @11
    @22
    @3
    @20
    @12
    @5
    cD
    nndivre
    syl2an
    @21
    cX
    @6
    flword2
    syl3anc
    jca
end
