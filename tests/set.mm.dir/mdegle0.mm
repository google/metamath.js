include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "clt.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "cxp.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "eqid.mm"
include "mdegleb.mm"
include "sylancl.mm"
include "cif.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "cr.mm"
include "wf.mm"
include "tdeglem1.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "ne0gt0.mm"
include "3syl.mm"
include "tdeglem4.mm"
include "sylan.mm"
include "necon3abid.mm"
include "bitr3d.mm"
include "imbi1d.mm"
include "eqeq2.mm"
include "bibi1d.mm"
include "fveq2.mm"
include "pm2.24.mm"
include "2thd.mm"
include "adantl.mm"
include "biimt.mm"
include "ifbothda.mm"
include "adantr.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "cbs.mm"
include "mplelf.mm"
include "feqmptd.mm"
include "psrbag0.mm"
include "ffvelrnd.mm"
include "mplascl.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "mp1i.mm"
include "bitrd.mm"

theorem mdegle0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegle0.b: |- B = ( Base ` Y )
  assume mdegle0.a: |- A = ( algSc ` Y )
  assume mdegle0.f: |- ( ph -> F e. B )


  assert |- ( ph -> ( ( D ` F ) <_ 0 <-> F = ( A ` ( F ` ( I X. { 0 } ) ) ) ) )

  proof
    wph
    cF
    cD
    cfv
    cc0
    cle
    wbr
    #
    cc0
    vx
    cv
    #
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    cfv
    #
    clt
    wbr
    #
    @1
    cF
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    @2
    wral
    #
    cF
    cI
    cc0
    csn
    cxp
    #
    cF
    cfv
    #
    cA
    cfv
    #
    wceq
    #
    wph
    cF
    cB
    wcel
    cc0
    cxr
    wcel
    @0
    @10
    wb
    mdegle0.f
    0xr
    vx
    @2
    cB
    cD
    cY
    cR
    vb
    va
    cF
    cc0
    @3
    cI
    @7
    mdegaddle.d
    mdegaddle.y
    mdegle0.b
    @7
    eqid
    #
    @2
    eqid
    #
    @3
    eqid
    #
    mdegleb
    sylancl
    wph
    @10
    @6
    @1
    @11
    wceq
    #
    @12
    @7
    cif
    #
    wceq
    #
    vx
    @2
    wral
    #
    @14
    wph
    @9
    @20
    vx
    @2
    wph
    @1
    @2
    wcel
    #
    wa
    #
    @9
    @18
    wn
    #
    @8
    wi
    #
    @20
    @23
    @5
    @24
    @8
    @23
    @4
    cc0
    wne
    #
    @5
    @24
    @23
    @4
    cn0
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    wa
    @26
    @5
    wb
    wph
    @2
    cn0
    @1
    @3
    wph
    cI
    cV
    wcel
    #
    @2
    cn0
    @3
    wf
    mdegaddle.i
    @2
    vb
    va
    @3
    cI
    cV
    @16
    @17
    tdeglem1
    syl
    ffvelrnda
    @27
    @28
    @29
    @4
    nn0re
    @4
    nn0ge0
    jca
    @4
    ne0gt0
    3syl
    @23
    @18
    @4
    cc0
    wph
    @30
    @22
    @4
    cc0
    wceq
    @18
    wb
    mdegaddle.i
    @2
    vb
    va
    @3
    cI
    cV
    @1
    @16
    @17
    tdeglem4
    sylan
    necon3abid
    bitr3d
    imbi1d
    wph
    @20
    @25
    wb
    #
    @22
    @18
    @6
    @12
    wceq
    #
    @25
    wb
    #
    @8
    @25
    wb
    #
    @31
    wph
    @12
    @7
    @12
    @19
    wceq
    @32
    @20
    @25
    @12
    @19
    @6
    eqeq2
    bibi1d
    @7
    @19
    wceq
    @8
    @20
    @25
    @7
    @19
    @6
    eqeq2
    bibi1d
    @18
    @33
    wph
    @18
    @32
    @25
    @1
    @11
    cF
    fveq2
    @18
    @8
    pm2.24
    2thd
    adantl
    @24
    @34
    wph
    @24
    @8
    biimt
    adantl
    ifbothda
    adantr
    bitr4d
    ralbidva
    wph
    @14
    vx
    @2
    @6
    cmpt
    #
    vx
    @2
    @19
    cmpt
    #
    wceq
    #
    @21
    wph
    cF
    @35
    @13
    @36
    wph
    vx
    @2
    cR
    cbs
    cfv
    #
    cF
    wph
    cB
    @2
    cY
    cR
    va
    cI
    @38
    cF
    mdegaddle.y
    @38
    eqid
    #
    mdegle0.b
    @16
    mdegle0.f
    mplelf
    #
    feqmptd
    wph
    vx
    cA
    @38
    @2
    cY
    cR
    va
    cI
    cV
    @12
    @7
    mdegaddle.y
    @16
    @15
    @39
    mdegle0.a
    mdegaddle.i
    mdegaddle.r
    wph
    @2
    @38
    @11
    cF
    @40
    wph
    @30
    @11
    @2
    wcel
    mdegaddle.i
    @2
    va
    cI
    cV
    @16
    psrbag0
    syl
    ffvelrnd
    mplascl
    eqeq12d
    @6
    cvv
    wcel
    #
    vx
    @2
    wral
    @37
    @21
    wb
    wph
    @41
    vx
    @2
    @1
    cF
    fvex
    rgenw
    vx
    @2
    @6
    @19
    cvv
    mpteqb
    mp1i
    bitrd
    bitr4d
    bitrd
end
