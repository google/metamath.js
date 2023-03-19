include "cusgr.mm"
include "wcel.mm"
include "ccplgr.mm"
include "ccusgr.mm"
include "structtousgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cvtx.mm"
include "wral.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "wne.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "eldifi.mm"
include "anim12ci.mm"
include "eldifsni.mm"
include "adantl.mm"
include "cid.mm"
include "cres.mm"
include "crn.mm"
include "cbs.mm"
include "cvv.mm"
include "fvexd.mm"
include "cnx.mm"
include "cedgf.mm"
include "cop.mm"
include "csts.mm"
include "fveq2i.mm"
include "eqid.mm"
include "fvex.mm"
include "cusgrexilem1.mm"
include "mp1i.mm"
include "setsvtx.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "adantr.mm"
include "wi.mm"
include "difeq1d.mm"
include "biimpd.mm"
include "imp.mm"
include "cusgrexilem2.mm"
include "syl21anc.mm"
include "wb.mm"
include "ciedg.mm"
include "edgval.mm"
include "setsiedg.mm"
include "rneqd.mm"
include "rexeqdv.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "nbgrel.mm"
include "syl3anbrc.mm"
include "ralrimiva.mm"
include "uvtxel.mm"
include "sylanbrc.mm"
include "elexd.mm"
include "iscplgr.mm"
include "syl.mm"
include "iscusgr.mm"

theorem structtocusgr
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cG: class G
  let cX: class X
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v
  assume structtousgr.p: |- P = { x e. ~P ( Base ` S ) | ( # ` x ) = 2 }
  assume structtousgr.s: |- ( ph -> S Struct X )
  assume structtousgr.g: |- G = ( S sSet <. ( .ef ` ndx ) , ( _I |` P ) >. )
  assume structtousgr.b: |- ( ph -> ( Base ` ndx ) e. dom S )

  disjoint G x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint G e
  disjoint G n
  disjoint G v
  disjoint e n
  disjoint e v
  disjoint n v
  disjoint P e
  disjoint P n
  disjoint P v
  disjoint e x
  disjoint n x
  disjoint v x
  disjoint S e
  disjoint S n
  disjoint S v
  disjoint n ph
  disjoint ph v
  assert |- ( ph -> G e. ComplUSGraph )

  proof
    wph
    cG
    cusgr
    wcel
    cG
    ccplgr
    wcel
    #
    cG
    ccusgr
    wcel
    wph
    vx
    cP
    cS
    cG
    cX
    structtousgr.p
    structtousgr.s
    structtousgr.g
    structtousgr.b
    structtousgr
    #
    wph
    @0
    vv
    cv
    #
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cG
    cvtx
    cfv
    #
    wral
    #
    wph
    @3
    vv
    @4
    wph
    @2
    @4
    wcel
    #
    wa
    #
    @6
    vn
    cv
    #
    cG
    @2
    cnbgr
    co
    wcel
    #
    vn
    @4
    @2
    csn
    #
    cdif
    #
    wral
    @3
    wph
    @6
    simpr
    #
    @7
    @9
    vn
    @11
    @7
    @8
    @11
    wcel
    #
    wa
    #
    @8
    @4
    wcel
    #
    @6
    wa
    @8
    @2
    wne
    #
    @2
    @8
    cpr
    ve
    cv
    wss
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    @9
    @7
    @6
    @13
    @15
    @12
    @8
    @4
    @10
    eldifi
    anim12ci
    @13
    @16
    @7
    @8
    @4
    @2
    eldifsni
    adantl
    @14
    @19
    @17
    ve
    cid
    cP
    cres
    #
    crn
    #
    wrex
    #
    @14
    cS
    cbs
    cfv
    #
    cvv
    wcel
    #
    @2
    @23
    wcel
    #
    @8
    @23
    @10
    cdif
    #
    wcel
    #
    @22
    @14
    cS
    cbs
    fvexd
    @7
    @25
    @13
    wph
    @6
    @25
    wph
    @4
    @23
    @2
    wph
    @4
    cS
    cnx
    cedgf
    cfv
    #
    @20
    cop
    csts
    co
    #
    cvtx
    cfv
    @23
    cG
    @29
    cvtx
    structtousgr.g
    fveq2i
    wph
    @20
    cS
    @28
    cvv
    cX
    @28
    eqid
    #
    structtousgr.s
    structtousgr.b
    @24
    @20
    cvv
    wcel
    wph
    cS
    cbs
    fvex
    vx
    cP
    @23
    cvv
    structtousgr.p
    cusgrexilem1
    mp1i
    #
    setsvtx
    syl5eq
    #
    eleq2d
    biimpa
    adantr
    @7
    @13
    @27
    wph
    @13
    @27
    wi
    @6
    wph
    @13
    @27
    wph
    @11
    @26
    @8
    wph
    @4
    @23
    @10
    @32
    difeq1d
    eleq2d
    biimpd
    adantr
    imp
    vx
    vv
    cP
    ve
    vn
    @23
    cvv
    structtousgr.p
    cusgrexilem2
    syl21anc
    wph
    @19
    @22
    wb
    @6
    @13
    wph
    @17
    ve
    @18
    @21
    wph
    @18
    cG
    ciedg
    cfv
    #
    crn
    @21
    cG
    edgval
    wph
    @33
    @20
    wph
    @33
    @29
    ciedg
    cfv
    @20
    cG
    @29
    ciedg
    structtousgr.g
    fveq2i
    wph
    @20
    cS
    @28
    cvv
    cX
    @30
    structtousgr.s
    structtousgr.b
    @31
    setsiedg
    syl5eq
    rneqd
    syl5eq
    rexeqdv
    ad2antrr
    mpbird
    ve
    @18
    cG
    @8
    @4
    @2
    @4
    eqid
    #
    @18
    eqid
    nbgrel
    syl3anbrc
    ralrimiva
    vn
    cG
    @2
    @4
    @34
    uvtxel
    sylanbrc
    ralrimiva
    wph
    cG
    cvv
    wcel
    @0
    @5
    wb
    wph
    cG
    cusgr
    @1
    elexd
    vv
    cG
    @4
    cvv
    @34
    iscplgr
    syl
    mpbird
    cG
    iscusgr
    sylanbrc
end
