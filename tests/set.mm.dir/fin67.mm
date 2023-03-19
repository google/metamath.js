include "cfin6.mm"
include "wcel.mm"
include "c2o.mm"
include "csdm.mm"
include "wbr.mm"
include "cxp.mm"
include "wo.mm"
include "cfin7.mm"
include "isfin6.mm"
include "cfn.mm"
include "cdom.mm"
include "com.mm"
include "wss.mm"
include "2onn.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "mp2an.mm"
include "sdomdom.mm"
include "domfi.mm"
include "sylancr.mm"
include "fin17.mm"
include "syl.mm"
include "cv.mm"
include "cen.mm"
include "con0.mm"
include "cdif.mm"
include "wrex.mm"
include "wn.mm"
include "sdomnen.mm"
include "wa.mm"
include "ccrd.mm"
include "cdm.mm"
include "eldifi.mm"
include "ensym.mm"
include "isnumi.mm"
include "syl2an.mm"
include "cvv.mm"
include "vex.mm"
include "eldif.mm"
include "word.mm"
include "wb.mm"
include "ordom.mm"
include "eloni.mm"
include "ordtri1.mm"
include "biimpar.mm"
include "sylbi.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "domen2.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "infxpidm2.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "nsyl.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "isfin7.mm"
include "mpbird.mm"
include "jaoi.mm"

theorem fin67
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin6 -> A e. Fin7 )

  proof
    cA
    cfin6
    wcel
    cA
    c2o
    csdm
    wbr
    #
    cA
    cA
    cA
    cxp
    #
    csdm
    wbr
    #
    wo
    cA
    cfin7
    wcel
    #
    cA
    isfin6
    @0
    @3
    @2
    @0
    cA
    cfn
    wcel
    #
    @3
    @0
    c2o
    cfn
    wcel
    #
    cA
    c2o
    cdom
    wbr
    @4
    c2o
    com
    wcel
    c2o
    c2o
    wss
    @5
    2onn
    c2o
    ssid
    c2o
    c2o
    ssnnfi
    mp2an
    cA
    c2o
    sdomdom
    c2o
    cA
    domfi
    sylancr
    cA
    fin17
    syl
    @2
    @3
    cA
    vb
    cv
    #
    cen
    wbr
    #
    vb
    con0
    com
    cdif
    #
    wrex
    #
    wn
    #
    @2
    cA
    @1
    cen
    wbr
    #
    @9
    cA
    @1
    sdomnen
    @7
    @11
    vb
    @8
    @6
    @8
    wcel
    #
    @7
    wa
    #
    @1
    cA
    cen
    wbr
    #
    @11
    @13
    cA
    ccrd
    cdm
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    @14
    @12
    @6
    con0
    wcel
    #
    @6
    cA
    cen
    wbr
    @15
    @7
    @6
    con0
    com
    eldifi
    cA
    @6
    ensym
    @6
    cA
    isnumi
    syl2an
    @7
    @12
    @16
    @12
    @16
    @7
    com
    @6
    cdom
    wbr
    #
    @6
    cvv
    wcel
    @12
    com
    @6
    wss
    #
    @18
    vb
    vex
    @12
    @17
    @6
    com
    wcel
    wn
    #
    wa
    @19
    @6
    con0
    com
    eldif
    @17
    @19
    @20
    @17
    com
    word
    @6
    word
    @19
    @20
    wb
    ordom
    @6
    eloni
    com
    @6
    ordtri1
    sylancr
    biimpar
    sylbi
    com
    @6
    cvv
    ssdomg
    mpsyl
    cA
    @6
    com
    domen2
    syl5ibr
    impcom
    cA
    infxpidm2
    syl2anc
    @1
    cA
    ensym
    syl
    rexlimiva
    nsyl
    @2
    cA
    cvv
    wcel
    @3
    @10
    wb
    cA
    @1
    csdm
    relsdom
    brrelexi
    vb
    cA
    cvv
    isfin7
    syl
    mpbird
    jaoi
    sylbi
end
