include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "eqidd.mm"
include "3mix1d.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eltpg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "a1i.mm"
include "dmeqd.mm"
include "dmun.mm"
include "dmpropg.mm"
include "syl2anc.mm"
include "dmsnopg.mm"
include "syl.mm"
include "uneq12d.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"
include "eleqtrrd.mm"

theorem estrreslem2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  assume estrres.c: |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )
  assume estrres.b: |- ( ph -> B e. V )
  assume estrres.h: |- ( ph -> H e. X )
  assume estrres.x: |- ( ph -> .x. e. Y )


  assert |- ( ph -> ( Base ` ndx ) e. dom C )

  proof
    wph
    cnx
    cbs
    cfv
    #
    @0
    cnx
    chom
    cfv
    #
    cnx
    cco
    cfv
    #
    ctp
    #
    cC
    cdm
    #
    wph
    @0
    @3
    wcel
    #
    @0
    @0
    wceq
    #
    @0
    @1
    wceq
    #
    @0
    @2
    wceq
    #
    w3o
    #
    wph
    @6
    @7
    @8
    wph
    @0
    eqidd
    3mix1d
    @0
    cvv
    wcel
    @5
    @9
    wb
    wph
    cnx
    cbs
    fvex
    @0
    @0
    @1
    @2
    cvv
    eltpg
    mp1i
    mpbird
    wph
    @0
    cB
    cop
    #
    @1
    cH
    cop
    #
    @2
    c.x
    cop
    #
    ctp
    #
    cdm
    #
    @0
    @1
    cpr
    #
    @2
    csn
    #
    cun
    #
    @4
    @3
    wph
    @14
    @10
    @11
    cpr
    #
    @12
    csn
    #
    cun
    #
    cdm
    #
    @18
    cdm
    #
    @19
    cdm
    #
    cun
    #
    @17
    wph
    @13
    @20
    @13
    @20
    wceq
    wph
    @10
    @11
    @12
    df-tp
    a1i
    dmeqd
    @21
    @24
    wceq
    wph
    @18
    @19
    dmun
    a1i
    wph
    @22
    @15
    @23
    @16
    wph
    cB
    cV
    wcel
    cH
    cX
    wcel
    @22
    @15
    wceq
    estrres.b
    estrres.h
    @0
    cB
    @1
    cH
    cV
    cX
    dmpropg
    syl2anc
    wph
    c.x
    cY
    wcel
    @23
    @16
    wceq
    estrres.x
    @2
    c.x
    cY
    dmsnopg
    syl
    uneq12d
    3eqtrd
    wph
    cC
    @13
    estrres.c
    dmeqd
    @3
    @17
    wceq
    wph
    @0
    @1
    @2
    df-tp
    a1i
    3eqtr4d
    eleqtrrd
end
