include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "wceq.mm"
include "cgcd.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "bezoutr.mm"
include "adantr.mm"
include "simpr.mm"
include "breqtrd.mm"
include "cn.mm"
include "wi.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "1nn.mm"
include "a1i.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "wb.mm"
include "cc0.mm"
include "wn.mm"
include "simpll.mm"
include "wne.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "zcn.mm"
include "mul02d.mm"
include "sylan9eqr.mm"
include "00id.mm"
include "syl6eq.mm"
include "adantll.mm"
include "0ne1.mm"
include "eqnetrd.mm"
include "ex.mm"
include "necon2bd.mm"
include "imp.mm"
include "gcdn0cl.mm"
include "nnle1eq1.mm"
include "syl.mm"
include "mpbid.mm"

theorem bezoutr1
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( X e. ZZ /\ Y e. ZZ ) ) -> ( ( ( A x. X ) + ( B x. Y ) ) = 1 -> ( A gcd B ) = 1 ) )

  proof
    cA
    cz
    wcel
    cB
    cz
    wcel
    wa
    #
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    cX
    cmul
    co
    #
    cB
    cY
    cmul
    co
    #
    caddc
    co
    #
    c1
    wceq
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    @4
    @8
    wa
    #
    @9
    c1
    cle
    wbr
    #
    @10
    @11
    @9
    c1
    cdvds
    wbr
    #
    @12
    @11
    @9
    @7
    c1
    cdvds
    @4
    @9
    @7
    cdvds
    wbr
    @8
    cA
    cB
    cX
    cY
    bezoutr
    adantr
    @4
    @8
    simpr
    breqtrd
    @11
    @9
    cz
    wcel
    #
    c1
    cn
    wcel
    #
    @13
    @12
    wi
    @0
    @14
    @3
    @8
    @0
    @9
    cA
    cB
    gcdcl
    nn0zd
    ad2antrr
    @15
    @11
    1nn
    a1i
    @9
    c1
    dvdsle
    syl2anc
    mpd
    @11
    @9
    cn
    wcel
    #
    @12
    @10
    wb
    @11
    @0
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @16
    @0
    @3
    @8
    simpll
    @4
    @8
    @20
    @4
    @19
    @7
    c1
    @4
    @19
    @7
    c1
    wne
    @4
    @19
    wa
    #
    @7
    cc0
    c1
    @3
    @19
    @7
    cc0
    wceq
    @0
    @3
    @19
    wa
    @7
    cc0
    cc0
    caddc
    co
    #
    cc0
    @19
    @3
    @7
    cc0
    cX
    cmul
    co
    #
    cc0
    cY
    cmul
    co
    #
    caddc
    co
    @22
    @17
    @18
    @5
    @23
    @6
    @24
    caddc
    cA
    cc0
    cX
    cmul
    oveq1
    cB
    cc0
    cY
    cmul
    oveq1
    oveqan12d
    @1
    @2
    @23
    cc0
    @24
    cc0
    caddc
    @1
    cX
    cX
    zcn
    mul02d
    @2
    cY
    cY
    zcn
    mul02d
    oveqan12d
    sylan9eqr
    00id
    syl6eq
    adantll
    cc0
    c1
    wne
    @21
    0ne1
    a1i
    eqnetrd
    ex
    necon2bd
    imp
    cA
    cB
    gcdn0cl
    syl2anc
    @9
    nnle1eq1
    syl
    mpbid
    ex
end
