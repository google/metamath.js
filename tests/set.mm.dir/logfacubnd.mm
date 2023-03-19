include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cfa.mm"
include "clog.mm"
include "cmul.mm"
include "co.mm"
include "cn0.mm"
include "cn.mm"
include "cr.mm"
include "rpre.mm"
include "flge1nn.mm"
include "sylan.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "adantr.mm"
include "reflcl.mm"
include "remulcld.mm"
include "relogcl.mm"
include "cexp.mm"
include "facubnd.mm"
include "nnexpcld.mm"
include "logled.mm"
include "mpbid.mm"
include "cz.mm"
include "wceq.mm"
include "nnzd.mm"
include "relogexp.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "flle.mm"
include "simpl.mm"
include "cc0.mm"
include "wi.mm"
include "rprege0d.mm"
include "log1.mm"
include "nnge1d.mm"
include "wb.mm"
include "1rp.mm"
include "logleb.mm"
include "sylancr.mm"
include "syl5eqbrr.mm"
include "jca.mm"
include "lemul12a.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "letrd.mm"

theorem logfacubnd
  let cA: class A
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x


  assert |- ( ( A e. RR+ /\ 1 <_ A ) -> ( log ` ( ! ` ( |_ ` A ) ) ) <_ ( A x. ( log ` A ) ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cfa
    cfv
    #
    clog
    cfv
    #
    @3
    @3
    clog
    cfv
    #
    cmul
    co
    #
    cA
    cA
    clog
    cfv
    #
    cmul
    co
    #
    @2
    @4
    @2
    @4
    @2
    @3
    cn0
    wcel
    #
    @4
    cn
    wcel
    @2
    @3
    @0
    cA
    cr
    wcel
    #
    @1
    @3
    cn
    wcel
    cA
    rpre
    #
    cA
    flge1nn
    sylan
    #
    nnnn0d
    #
    @3
    faccl
    syl
    nnrpd
    #
    relogcld
    @2
    @3
    @6
    @2
    @11
    @3
    cr
    wcel
    #
    @0
    @11
    @1
    @12
    adantr
    #
    cA
    reflcl
    syl
    @2
    @3
    @2
    @3
    @13
    nnrpd
    #
    relogcld
    #
    remulcld
    @2
    cA
    @8
    @17
    @0
    @8
    cr
    wcel
    #
    @1
    cA
    relogcl
    adantr
    #
    remulcld
    @2
    @5
    @3
    @3
    cexp
    co
    #
    clog
    cfv
    #
    @7
    cle
    @2
    @4
    @22
    cle
    wbr
    #
    @5
    @23
    cle
    wbr
    @2
    @10
    @24
    @14
    @3
    facubnd
    syl
    @2
    @4
    @22
    @15
    @2
    @22
    @2
    @3
    @3
    @13
    @14
    nnexpcld
    nnrpd
    logled
    mpbid
    @2
    @3
    crp
    wcel
    #
    @3
    cz
    wcel
    @23
    @7
    wceq
    @18
    @2
    @3
    @13
    nnzd
    @3
    @3
    relogexp
    syl2anc
    breqtrd
    @2
    @3
    cA
    cle
    wbr
    #
    @6
    @8
    cle
    wbr
    #
    @7
    @9
    cle
    wbr
    #
    @2
    @11
    @26
    @17
    cA
    flle
    syl
    #
    @2
    @26
    @27
    @29
    @2
    @3
    cA
    @18
    @0
    @1
    simpl
    logled
    mpbid
    @2
    @16
    cc0
    @3
    cle
    wbr
    wa
    @11
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    @20
    @26
    @27
    wa
    @28
    wi
    @2
    @3
    @18
    rprege0d
    @17
    @2
    @30
    @31
    @19
    @2
    cc0
    c1
    clog
    cfv
    #
    @6
    cle
    log1
    @2
    c1
    @3
    cle
    wbr
    #
    @32
    @6
    cle
    wbr
    #
    @2
    @3
    @13
    nnge1d
    @2
    c1
    crp
    wcel
    @25
    @33
    @34
    wb
    1rp
    @18
    c1
    @3
    logleb
    sylancr
    mpbid
    syl5eqbrr
    jca
    @21
    @3
    cA
    @6
    @8
    lemul12a
    syl22anc
    mp2and
    letrd
end
