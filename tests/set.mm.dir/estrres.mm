include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "cbs.mm"
include "cco.mm"
include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "setsval.mm"
include "sylancr.mm"
include "eqid.mm"
include "tpex.mm"
include "syl6eqel.mm"
include "wfun.mm"
include "w3a.mm"
include "wne.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "slotsbhcdif.mm"
include "funtpg.mm"
include "syl131anc.mm"
include "funeqd.mm"
include "mpbird.mm"
include "estrreslem2.mm"
include "estrreslem1.mm"
include "sseqtrd.mm"
include "ressval3d.mm"
include "reseq1d.mm"
include "uneq1d.mm"
include "cpr.mm"
include "syl2anc.mm"
include "elex.mm"
include "syl.mm"
include "simp1.mm"
include "necomd.mm"
include "mp1i.mm"
include "simp2.mm"
include "tpres.mm"
include "df-tp.mm"
include "syl6eqr.mm"
include "ssexd.mm"
include "simp3.mm"
include "eqtrd.mm"
include "tprot.mm"
include "eqtr3i.mm"

theorem estrres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume estrres.c: |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )
  assume estrres.b: |- ( ph -> B e. V )
  assume estrres.h: |- ( ph -> H e. X )
  assume estrres.x: |- ( ph -> .x. e. Y )
  assume estrres.a: |- ( ph -> A e. U )
  assume estrres.g: |- ( ph -> G e. W )
  assume estrres.u: |- ( ph -> A C_ B )


  assert |- ( ph -> ( ( C |`s A ) sSet <. ( Hom ` ndx ) , G >. ) = { <. ( Base ` ndx ) , A >. , <. ( Hom ` ndx ) , G >. , <. ( comp ` ndx ) , .x. >. } )

  proof
    wph
    cC
    cA
    cress
    co
    #
    cnx
    chom
    cfv
    #
    cG
    cop
    #
    csts
    co
    #
    @0
    cvv
    @1
    csn
    cdif
    #
    cres
    #
    @2
    csn
    #
    cun
    #
    cnx
    cbs
    cfv
    #
    cA
    cop
    #
    @2
    cnx
    cco
    cfv
    #
    c.x
    cop
    #
    ctp
    #
    wph
    @0
    cvv
    wcel
    cG
    cW
    wcel
    @3
    @7
    wceq
    cC
    cA
    cress
    ovex
    estrres.g
    @1
    cG
    @0
    cvv
    cW
    setsval
    sylancr
    wph
    @7
    cC
    @9
    csts
    co
    #
    @4
    cres
    #
    @6
    cun
    #
    @12
    wph
    @5
    @14
    @6
    wph
    @0
    @13
    @4
    wph
    cA
    cC
    cbs
    cfv
    #
    @0
    cC
    @8
    cvv
    cU
    @0
    eqid
    @16
    eqid
    @8
    eqid
    wph
    cC
    @8
    cB
    cop
    #
    @1
    cH
    cop
    #
    @11
    ctp
    #
    cvv
    estrres.c
    @17
    @18
    @11
    tpex
    syl6eqel
    #
    wph
    cC
    wfun
    @19
    wfun
    #
    wph
    @8
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    w3a
    #
    cB
    cV
    wcel
    cH
    cX
    wcel
    #
    c.x
    cY
    wcel
    #
    @8
    @1
    wne
    #
    @8
    @10
    wne
    #
    @1
    @10
    wne
    #
    w3a
    #
    @21
    @25
    wph
    @22
    @23
    @24
    cnx
    cbs
    fvex
    #
    cnx
    chom
    fvex
    #
    cnx
    cco
    fvex
    #
    3pm3.2i
    a1i
    estrres.b
    estrres.h
    estrres.x
    @31
    wph
    slotsbhcdif
    a1i
    cB
    cH
    c.x
    cvv
    cV
    cX
    cY
    cvv
    cvv
    @8
    @1
    @10
    funtpg
    syl131anc
    wph
    cC
    @19
    estrres.c
    funeqd
    mpbird
    wph
    cB
    cC
    c.x
    cH
    cV
    cX
    cY
    estrres.c
    estrres.b
    estrres.h
    estrres.x
    estrreslem2
    estrres.a
    wph
    cA
    cB
    @16
    estrres.u
    wph
    cB
    cC
    c.x
    cH
    cV
    estrres.c
    estrres.b
    estrreslem1
    sseqtrd
    ressval3d
    reseq1d
    uneq1d
    wph
    @15
    @11
    @9
    cpr
    #
    @6
    cun
    #
    @12
    wph
    @14
    @35
    @6
    wph
    @14
    cC
    cvv
    @8
    csn
    cdif
    cres
    #
    @9
    csn
    #
    cun
    #
    @4
    cres
    @35
    wph
    @13
    @39
    @4
    wph
    cC
    cvv
    wcel
    cA
    cU
    wcel
    @13
    @39
    wceq
    @20
    estrres.a
    @8
    cA
    cC
    cvv
    cU
    setsval
    syl2anc
    reseq1d
    wph
    @1
    @10
    @8
    cH
    @39
    c.x
    cA
    cvv
    wph
    @39
    @18
    @11
    cpr
    #
    @38
    cun
    @18
    @11
    @9
    ctp
    wph
    @37
    @40
    @38
    wph
    @8
    @1
    @10
    cB
    cC
    cH
    c.x
    cvv
    estrres.c
    @23
    wph
    @33
    a1i
    @24
    wph
    @34
    a1i
    #
    wph
    @26
    cH
    cvv
    wcel
    estrres.h
    cH
    cX
    elex
    syl
    wph
    @27
    c.x
    cvv
    wcel
    estrres.x
    c.x
    cY
    elex
    syl
    #
    @31
    @1
    @8
    wne
    wph
    slotsbhcdif
    @31
    @8
    @1
    @28
    @29
    @30
    simp1
    #
    necomd
    mp1i
    @31
    @10
    @8
    wne
    wph
    slotsbhcdif
    @31
    @8
    @10
    @28
    @29
    @30
    simp2
    necomd
    mp1i
    tpres
    uneq1d
    @18
    @11
    @9
    df-tp
    syl6eqr
    @41
    @22
    wph
    @32
    a1i
    @42
    wph
    cA
    cB
    cV
    estrres.b
    estrres.u
    ssexd
    @31
    @10
    @1
    wne
    wph
    slotsbhcdif
    @31
    @1
    @10
    @28
    @29
    @30
    simp3
    necomd
    mp1i
    @31
    @28
    wph
    slotsbhcdif
    @43
    mp1i
    tpres
    eqtrd
    uneq1d
    @36
    @12
    wceq
    wph
    @11
    @9
    @2
    ctp
    @36
    @12
    @11
    @9
    @2
    df-tp
    @11
    @9
    @2
    tprot
    eqtr3i
    a1i
    eqtrd
    eqtrd
    eqtrd
end
