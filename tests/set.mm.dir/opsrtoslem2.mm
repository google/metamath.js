include "cbs.mm"
include "cfv.mm"
include "cplt.mm"
include "wor.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "ctos.mm"
include "wcel.mm"
include "copab.mm"
include "cxp.mm"
include "cin.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wwe.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "ovex.mm"
include "rabex2.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexd.mm"
include "ltbwe.mm"
include "cple.mm"
include "wa.mm"
include "eqid.mm"
include "tosso.mm"
include "ibi.mm"
include "syl.mm"
include "simpld.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "opabbii.mm"
include "wemapso.mm"
include "mp3an2i.mm"
include "wb.mm"
include "psrbas.mm"
include "soeq2.mm"
include "mpbird.mm"
include "soinxp.mm"
include "sylib.mm"
include "cdif.mm"
include "copws.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pltfval.mm"
include "ax-mp.mm"
include "cun.mm"
include "c0.mm"
include "difundir.mm"
include "resss.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "opsrtoslem1.mm"
include "difeq1d.mm"
include "wrel.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "cop.mm"
include "wn.mm"
include "df-br.mm"
include "vex.mm"
include "ideq.mm"
include "bitr3i.mm"
include "brin.mm"
include "simprbi.mm"
include "brxp.mm"
include "sonr.mm"
include "ex.mm"
include "syl2im.mm"
include "pm2.01d.mm"
include "breq2.mm"
include "syl6bb.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "syl5bi.mm"
include "con2d.mm"
include "opex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "syl6ibr.mm"
include "relssdv.mm"
include "disj2.mm"
include "sylibr.mm"
include "disj3.mm"
include "3eqtr4a.mm"
include "syl5eq.mm"
include "soeq1.mm"
include "opsrbas.mm"
include "mpbid.mm"
include "reseq2d.mm"
include "ssun2.mm"
include "syl6eqssr.mm"
include "sseqtr4d.mm"
include "sylanbrc.mm"

theorem opsrtoslem2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cT: class T
  let vh: setvar h
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume opsrso.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrso.i: |- ( ph -> I e. V )
  assume opsrso.r: |- ( ph -> R e. Toset )
  assume opsrso.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrso.w: |- ( ph -> T We I )
  assume opsrtoslem.s: |- S = ( I mPwSer R )
  assume opsrtoslem.b: |- B = ( Base ` S )
  assume opsrtoslem.q: |- .< = ( lt ` R )
  assume opsrtoslem.c: |- C = ( T <bag I )
  assume opsrtoslem.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume opsrtoslem.ps: |- ( ps <-> E. z e. D ( ( x ` z ) .< ( y ` z ) /\ A. w e. D ( w C z -> ( x ` w ) = ( y ` w ) ) ) )
  assume opsrtoslem.l: |- .<_ = ( le ` O )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint .< w
  disjoint .< x
  disjoint .< y
  disjoint .< z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint a h
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b h
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint a ps
  disjoint b ps
  assert |- ( ph -> O e. Toset )

  proof
    wph
    cO
    cbs
    cfv
    #
    cO
    cplt
    cfv
    #
    wor
    #
    cid
    @0
    cres
    #
    c.le
    wss
    #
    cO
    ctos
    wcel
    #
    wph
    cB
    @1
    wor
    #
    @2
    wph
    @6
    cB
    wps
    vx
    vy
    copab
    #
    cB
    cB
    cxp
    #
    cin
    #
    wor
    #
    wph
    cB
    @7
    wor
    #
    @10
    wph
    @11
    cR
    cbs
    cfv
    #
    cD
    cmap
    co
    #
    @7
    wor
    #
    cD
    cvv
    wcel
    wph
    cD
    cC
    wwe
    @12
    c.lt
    wor
    #
    @14
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    opsrtoslem.d
    cn0
    cI
    cmap
    ovex
    rabex2
    wph
    cC
    cD
    cT
    vh
    cI
    cV
    cvv
    opsrtoslem.c
    opsrtoslem.d
    opsrso.i
    wph
    cT
    cI
    cI
    cxp
    #
    cvv
    wph
    cI
    cV
    wcel
    #
    @17
    @16
    cvv
    wcel
    opsrso.i
    opsrso.i
    cI
    cI
    cV
    cV
    xpexg
    syl2anc
    opsrso.t
    ssexd
    opsrso.w
    ltbwe
    wph
    @15
    cid
    @12
    cres
    cR
    cple
    cfv
    #
    wss
    #
    wph
    cR
    ctos
    wcel
    #
    @15
    @19
    wa
    #
    opsrso.r
    @20
    @21
    @12
    c.lt
    cR
    @18
    ctos
    @12
    eqid
    #
    @18
    eqid
    opsrtoslem.q
    tosso
    ibi
    syl
    simpld
    vx
    vy
    vz
    vw
    cD
    @12
    cC
    c.lt
    @7
    cvv
    wps
    vz
    cv
    #
    vx
    cv
    #
    cfv
    @23
    vy
    cv
    #
    cfv
    c.lt
    wbr
    vw
    cv
    #
    @23
    cC
    wbr
    @26
    @24
    cfv
    @26
    @25
    cfv
    wceq
    wi
    vw
    cD
    wral
    wa
    vz
    cD
    wrex
    vx
    vy
    opsrtoslem.ps
    opabbii
    wemapso
    mp3an2i
    wph
    cB
    @13
    wceq
    @11
    @14
    wb
    wph
    cB
    cD
    cR
    cS
    vh
    cI
    @12
    cV
    opsrtoslem.s
    @22
    opsrtoslem.d
    opsrtoslem.b
    opsrso.i
    psrbas
    cB
    @13
    @7
    soeq2
    syl
    mpbird
    cB
    @7
    soinxp
    sylib
    #
    wph
    @1
    @9
    wceq
    @6
    @10
    wb
    wph
    @1
    c.le
    cid
    cdif
    #
    @9
    cO
    cvv
    wcel
    #
    @1
    @28
    wceq
    cO
    cT
    cI
    cR
    copws
    co
    #
    cfv
    cvv
    opsrso.o
    cT
    @30
    fvex
    eqeltri
    #
    cvv
    @1
    cO
    c.le
    opsrtoslem.l
    @1
    eqid
    #
    pltfval
    ax-mp
    wph
    @9
    cid
    cB
    cres
    #
    cun
    #
    cid
    cdif
    #
    @9
    cid
    cdif
    #
    @28
    @9
    @35
    @36
    @33
    cid
    cdif
    #
    cun
    @36
    c0
    cun
    @36
    @9
    @33
    cid
    difundir
    @37
    c0
    @36
    @33
    cid
    wss
    @37
    c0
    wceq
    cid
    cB
    resss
    @33
    cid
    ssdif0
    mpbi
    uneq2i
    @36
    un0
    3eqtri
    wph
    c.le
    @34
    cid
    wph
    wps
    vx
    vy
    vz
    vw
    cB
    cC
    cD
    cR
    cS
    c.lt
    cT
    vh
    cI
    c.le
    cO
    cV
    opsrso.o
    opsrso.i
    opsrso.r
    opsrso.t
    opsrso.w
    opsrtoslem.s
    opsrtoslem.b
    opsrtoslem.q
    opsrtoslem.c
    opsrtoslem.d
    opsrtoslem.ps
    opsrtoslem.l
    opsrtoslem1
    #
    difeq1d
    wph
    @9
    cid
    cin
    c0
    wceq
    #
    @9
    @36
    wceq
    wph
    @9
    cvv
    cid
    cdif
    #
    wss
    @39
    wph
    va
    vb
    @9
    @40
    @9
    wrel
    #
    wph
    @9
    @8
    wss
    @8
    wrel
    @41
    @7
    @8
    inss2
    cB
    cB
    relxp
    @9
    @8
    relss
    mp2
    a1i
    wph
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    @9
    wcel
    #
    @44
    cid
    wcel
    #
    wn
    #
    @44
    @40
    wcel
    #
    wph
    @46
    @45
    @46
    @42
    @43
    wceq
    #
    wph
    @45
    wn
    #
    @46
    @42
    @43
    cid
    wbr
    @49
    @42
    @43
    cid
    df-br
    @42
    @43
    vb
    vex
    ideq
    bitr3i
    wph
    @42
    @42
    @9
    wbr
    #
    wn
    #
    @49
    @50
    wph
    @51
    wph
    @10
    @51
    @42
    cB
    wcel
    #
    @52
    @27
    @51
    @42
    @42
    @8
    wbr
    #
    @53
    @51
    @42
    @42
    @7
    wbr
    @54
    @42
    @42
    @7
    @8
    brin
    simprbi
    @54
    @53
    @53
    @42
    @42
    cB
    cB
    brxp
    simprbi
    syl
    @10
    @53
    @52
    cB
    @42
    @9
    sonr
    ex
    syl2im
    pm2.01d
    @49
    @51
    @45
    @49
    @51
    @42
    @43
    @9
    wbr
    @45
    @42
    @43
    @42
    @9
    breq2
    @42
    @43
    @9
    df-br
    syl6bb
    notbid
    syl5ibcom
    syl5bi
    con2d
    @48
    @44
    cvv
    wcel
    @47
    @42
    @43
    opex
    @44
    cvv
    cid
    eldif
    mpbiran
    syl6ibr
    relssdv
    @9
    cid
    disj2
    sylibr
    @9
    cid
    disj3
    sylib
    3eqtr4a
    syl5eq
    cB
    @1
    @9
    soeq1
    syl
    mpbird
    wph
    cB
    @0
    wceq
    @6
    @2
    wb
    wph
    cB
    cS
    cbs
    cfv
    @0
    opsrtoslem.b
    wph
    cR
    cS
    cT
    cI
    cO
    opsrtoslem.s
    opsrso.o
    opsrso.t
    opsrbas
    syl5eq
    #
    cB
    @0
    @1
    soeq2
    syl
    mpbid
    wph
    @3
    @34
    c.le
    wph
    @3
    @33
    @34
    wph
    cB
    @0
    cid
    @55
    reseq2d
    @33
    @9
    ssun2
    syl6eqssr
    @38
    sseqtr4d
    @29
    @5
    @2
    @4
    wa
    wb
    @31
    @0
    @1
    cO
    c.le
    cvv
    @0
    eqid
    opsrtoslem.l
    @32
    tosso
    ax-mp
    sylanbrc
end
