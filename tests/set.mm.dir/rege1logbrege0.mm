include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cico.mm"
include "wa.mm"
include "cc0.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "clogb.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "id.mm"
include "sylbi.mm"
include "adantl.mm"
include "logge0.mm"
include "syl.mm"
include "clt.mm"
include "crp.mm"
include "simpl.mm"
include "0lt1.mm"
include "wi.mm"
include "0red.mm"
include "1red.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "imp.mm"
include "elrpd.mm"
include "relogcld.mm"
include "cxr.mm"
include "rexri.mm"
include "elioopnf.mm"
include "lttr.mm"
include "adantr.mm"
include "regt1loggt0.mm"
include "ge0div.mm"
include "mpbid.mm"
include "cc.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "recn.mm"
include "gt0ne0d.mm"
include "ltlend.mm"
include "simplbda.mm"
include "3jca.mm"
include "eldifpr.mm"
include "3imtr4i.mm"
include "jca.mm"
include "eldifsn.mm"
include "logbval.mm"
include "syl2an.mm"
include "breqtrrd.mm"

theorem rege1logbrege0
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( 1 (,) +oo ) /\ X e. ( 1 [,) +oo ) ) -> 0 <_ ( B logb X ) )

  proof
    cB
    c1
    cpnf
    cioo
    co
    wcel
    #
    cX
    c1
    cpnf
    cico
    co
    wcel
    #
    wa
    #
    cc0
    cX
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cB
    cX
    clogb
    co
    #
    cle
    @2
    cc0
    @3
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    @2
    cX
    cr
    wcel
    #
    c1
    cX
    cle
    wbr
    #
    wa
    #
    @7
    @1
    @11
    @0
    @1
    @11
    @11
    c1
    cr
    wcel
    #
    @1
    @11
    wb
    1re
    c1
    cX
    elicopnf
    ax-mp
    #
    @11
    id
    sylbi
    adantl
    cX
    logge0
    syl
    @2
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @7
    @8
    wb
    @1
    @14
    @0
    @1
    cX
    @1
    @11
    cX
    crp
    wcel
    @13
    @11
    cX
    @9
    @10
    simpl
    @9
    @10
    cc0
    cX
    clt
    wbr
    #
    @9
    cc0
    c1
    clt
    wbr
    #
    @10
    @17
    0lt1
    @9
    cc0
    cr
    wcel
    #
    @12
    @9
    @18
    @10
    wa
    @17
    wi
    @9
    0red
    @9
    1red
    @9
    id
    cc0
    c1
    cX
    ltletr
    syl3anc
    mpani
    imp
    #
    elrpd
    sylbi
    relogcld
    adantl
    @0
    @15
    @1
    @0
    cB
    @0
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    wa
    #
    cB
    crp
    wcel
    c1
    cxr
    wcel
    @0
    @23
    wb
    c1
    1re
    rexri
    c1
    cB
    elioopnf
    ax-mp
    #
    @23
    cB
    @21
    @22
    simpl
    @21
    @22
    cc0
    cB
    clt
    wbr
    #
    @21
    @18
    @22
    @25
    0lt1
    @21
    @19
    @12
    @21
    @18
    @22
    wa
    @25
    wi
    @21
    0red
    @21
    1red
    #
    @21
    id
    #
    cc0
    c1
    cB
    lttr
    syl3anc
    mpani
    imp
    #
    elrpd
    sylbi
    relogcld
    adantr
    @0
    @16
    @1
    cB
    regt1loggt0
    adantr
    @3
    @4
    ge0div
    syl3anc
    mpbid
    @0
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cX
    cc
    cc0
    csn
    cdif
    wcel
    #
    @6
    @5
    wceq
    @1
    @23
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    @0
    @29
    @23
    @31
    @32
    @33
    @21
    @31
    @22
    cB
    recn
    adantr
    @23
    cB
    @28
    gt0ne0d
    @21
    @22
    c1
    cB
    cle
    wbr
    @33
    @21
    c1
    cB
    @26
    @27
    ltlend
    simplbda
    3jca
    @24
    cB
    cc
    cc0
    c1
    eldifpr
    3imtr4i
    @11
    cX
    cc
    wcel
    #
    cX
    cc0
    wne
    #
    wa
    @1
    @30
    @11
    @34
    @35
    @9
    @34
    @10
    cX
    recn
    adantr
    @11
    cX
    @20
    gt0ne0d
    jca
    @13
    cX
    cc
    cc0
    eldifsn
    3imtr4i
    cB
    cX
    logbval
    syl2an
    breqtrrd
end
