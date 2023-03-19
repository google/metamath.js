include "csdm.mm"
include "wbr.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cdom.mm"
include "wa.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "sdomdom.mm"
include "cvv.mm"
include "wb.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "brdomg.mm"
include "syl.mm"
include "mpbid.mm"
include "adantr.mm"
include "crn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "adantl.mm"
include "cen.mm"
include "wn.mm"
include "sdomnen.mm"
include "ad2antrr.mm"
include "wi.mm"
include "wceq.mm"
include "wf1o.mm"
include "vex.mm"
include "dff1o5.mm"
include "biimpri.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"
include "pssdifn0.mm"
include "syl2anc.mm"
include "n0.mm"
include "sylib.mm"
include "brrelexi.mm"
include "difexg.mm"
include "cin.mm"
include "eldifn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "reldisj.mm"
include "f1ssr.mm"
include "syldan.mm"
include "f1dom2g.mm"
include "syl3anc.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "simplr.mm"
include "difsnen.mm"
include "domentr.mm"
include "expr.mm"
include "exlimdv.mm"
include "exlimddv.mm"
include "difsn.mm"
include "breq2d.mm"
include "mpbird.mm"
include "pm2.61dan.mm"

theorem domdifsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x


  assert |- ( A ~< B -> A ~<_ ( B \ { C } ) )

  proof
    cA
    cB
    csdm
    wbr
    #
    cC
    cB
    wcel
    #
    cA
    cB
    cC
    csn
    cdif
    #
    cdom
    wbr
    #
    @0
    @1
    wa
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    @3
    vf
    @0
    @6
    vf
    wex
    #
    @1
    @0
    cA
    cB
    cdom
    wbr
    #
    @7
    cA
    cB
    sdomdom
    #
    @0
    cB
    cvv
    wcel
    #
    @8
    @7
    wb
    cA
    cB
    csdm
    relsdom
    brrelex2i
    #
    cA
    cB
    cvv
    vf
    brdomg
    syl
    mpbid
    adantr
    @4
    @6
    wa
    #
    vx
    cv
    #
    cB
    @5
    crn
    #
    cdif
    #
    wcel
    #
    vx
    wex
    #
    @3
    @12
    @15
    c0
    wne
    #
    @17
    @12
    @14
    cB
    wss
    #
    @14
    cB
    wne
    #
    @18
    @6
    @19
    @4
    @6
    cA
    cB
    @5
    wf
    @19
    cA
    cB
    @5
    f1f
    cA
    cB
    @5
    frn
    syl
    #
    adantl
    @12
    cA
    cB
    cen
    wbr
    #
    wn
    #
    @20
    @0
    @23
    @1
    @6
    cA
    cB
    sdomnen
    ad2antrr
    @6
    @23
    @20
    wi
    @4
    @6
    @22
    @14
    cB
    @6
    @14
    cB
    wceq
    #
    @22
    @6
    @24
    wa
    #
    @5
    cvv
    wcel
    cA
    cB
    @5
    wf1o
    #
    @22
    vf
    vex
    @26
    @25
    cA
    cB
    @5
    dff1o5
    biimpri
    cA
    cB
    @5
    cvv
    f1oen3g
    sylancr
    ex
    necon3bd
    adantl
    mpd
    @14
    cB
    pssdifn0
    syl2anc
    vx
    @15
    n0
    sylib
    @12
    @16
    @3
    vx
    @4
    @6
    @16
    @3
    @4
    @6
    @16
    wa
    #
    wa
    #
    cA
    cB
    @13
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @30
    @2
    cen
    wbr
    #
    @3
    @28
    cA
    cvv
    wcel
    #
    @30
    cvv
    wcel
    #
    cA
    @30
    @5
    wf1
    #
    @31
    @0
    @33
    @1
    @27
    cA
    cB
    csdm
    relsdom
    brrelexi
    ad2antrr
    @28
    @10
    @34
    @0
    @10
    @1
    @27
    @11
    ad2antrr
    #
    cB
    @29
    cvv
    difexg
    syl
    @27
    @35
    @4
    @6
    @16
    @14
    @30
    wss
    #
    @35
    @27
    @14
    @29
    cin
    c0
    wceq
    #
    @37
    @16
    @38
    @6
    @16
    @13
    @14
    wcel
    wn
    @38
    @13
    cB
    @14
    eldifn
    @14
    @13
    disjsn
    sylibr
    adantl
    @27
    @19
    @38
    @37
    wb
    @6
    @19
    @16
    @21
    adantr
    @14
    @29
    cB
    reldisj
    syl
    mpbid
    cA
    cB
    @30
    @5
    f1ssr
    syldan
    adantl
    cA
    @30
    @5
    cvv
    cvv
    f1dom2g
    syl3anc
    @28
    @10
    @13
    cB
    wcel
    #
    @1
    @32
    @36
    @16
    @39
    @4
    @6
    @13
    cB
    @14
    eldifi
    ad2antll
    @0
    @1
    @27
    simplr
    @13
    cC
    cvv
    cB
    difsnen
    syl3anc
    cA
    @30
    @2
    domentr
    syl2anc
    expr
    exlimdv
    mpd
    exlimddv
    @0
    @1
    wn
    #
    wa
    @3
    @8
    @0
    @8
    @40
    @9
    adantr
    @40
    @3
    @8
    wb
    @0
    @40
    @2
    cB
    cA
    cdom
    cC
    cB
    difsn
    breq2d
    adantl
    mpbird
    pm2.61dan
end
