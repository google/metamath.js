include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cn0.mm"
include "wcel.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "ceupth.mm"
include "cwlks.mm"
include "eupthiswlk.mm"
include "wlkcl.mm"
include "3syl.mm"
include "nn0p1elfzo.mm"
include "syl3anc.mm"
include "ctrls.mm"
include "eupthistrl.mm"
include "syl.mm"
include "cvtx.mm"
include "wceq.mm"
include "cima.mm"
include "cres.mm"
include "fveq2i.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "resex.mm"
include "opvtxfvi.mm"
include "eqtri.mm"
include "a1i.mm"
include "snex.mm"
include "opiedgfvi.mm"
include "cfz.mm"
include "cz.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "imaeq2d.mm"
include "reseq2d.mm"
include "syl5eq.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "cupgr.mm"
include "upgrwlkedg.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eupth2lem3lem7.mm"

theorem eupth2lem3
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume eupth2.v: |- V = ( Vtx ` G )
  assume eupth2.i: |- I = ( iEdg ` G )
  assume eupth2.g: |- ( ph -> G e. UPGraph )
  assume eupth2.f: |- ( ph -> Fun I )
  assume eupth2.p: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eupth2.h: |- H = <. V , ( I |` ( F " ( 0 ..^ N ) ) ) >.
  assume eupth2.x: |- X = <. V , ( I |` ( F " ( 0 ..^ ( N + 1 ) ) ) ) >.
  assume eupth2.n: |- ( ph -> N e. NN0 )
  assume eupth2.l: |- ( ph -> ( N + 1 ) <_ ( # ` F ) )
  assume eupth2.u: |- ( ph -> U e. V )
  assume eupth2.o: |- ( ph -> { x e. V | -. 2 || ( ( VtxDeg ` H ) ` x ) } = if ( ( P ` 0 ) = ( P ` N ) , (/) , { ( P ` 0 ) , ( P ` N ) } ) )

  disjoint H x
  disjoint U x
  disjoint V x
  disjoint F k
  disjoint G k
  disjoint I k
  disjoint N k
  disjoint P k
  assert |- ( ph -> ( -. 2 || ( ( VtxDeg ` X ) ` U ) <-> U e. if ( ( P ` 0 ) = ( P ` ( N + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( N + 1 ) ) } ) ) )

  proof
    wph
    vx
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cH
    cV
    cN
    cF
    cfv
    #
    @0
    cI
    cfv
    #
    cop
    #
    csn
    #
    cop
    #
    cX
    eupth2.v
    eupth2.i
    eupth2.f
    wph
    cN
    cn0
    wcel
    cF
    chash
    cfv
    #
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    @5
    cle
    wbr
    cN
    cc0
    @5
    cfzo
    co
    #
    wcel
    #
    eupth2.n
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @6
    eupth2.p
    cP
    cF
    cG
    eupthiswlk
    #
    cP
    cF
    cG
    wlkcl
    3syl
    eupth2.l
    cN
    @5
    nn0p1elfzo
    syl3anc
    #
    eupth2.u
    wph
    @10
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    eupth2.p
    cP
    cF
    cG
    eupthistrl
    syl
    cH
    cvtx
    cfv
    #
    cV
    wceq
    wph
    @14
    cV
    cI
    cF
    cc0
    cN
    cfzo
    co
    cima
    #
    cres
    #
    cop
    #
    cvtx
    cfv
    cV
    cH
    @17
    cvtx
    eupth2.h
    fveq2i
    @16
    cV
    cV
    cG
    cvtx
    cfv
    cvv
    eupth2.v
    cG
    cvtx
    fvex
    eqeltri
    #
    cI
    @15
    cI
    cG
    ciedg
    cfv
    cvv
    eupth2.i
    cG
    ciedg
    fvex
    eqeltri
    #
    resex
    #
    opvtxfvi
    eqtri
    a1i
    @4
    cvtx
    cfv
    cV
    wceq
    wph
    @3
    cV
    @18
    @2
    snex
    #
    opvtxfvi
    a1i
    cX
    cvtx
    cfv
    #
    cV
    wceq
    wph
    @22
    cV
    cI
    cF
    cc0
    @7
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtx
    cfv
    cV
    cX
    @26
    cvtx
    eupth2.x
    fveq2i
    @25
    cV
    @18
    cI
    @24
    @19
    resex
    #
    opvtxfvi
    eqtri
    a1i
    cH
    ciedg
    cfv
    #
    @16
    wceq
    wph
    @28
    @17
    ciedg
    cfv
    @16
    cH
    @17
    ciedg
    eupth2.h
    fveq2i
    @16
    cV
    @18
    @20
    opiedgfvi
    eqtri
    a1i
    @4
    ciedg
    cfv
    @3
    wceq
    wph
    @3
    cV
    @18
    @21
    opiedgfvi
    a1i
    wph
    cX
    ciedg
    cfv
    #
    @25
    cI
    cF
    cc0
    cN
    cfz
    co
    #
    cima
    #
    cres
    @29
    @26
    ciedg
    cfv
    @25
    cX
    @26
    ciedg
    eupth2.x
    fveq2i
    @25
    cV
    @18
    @27
    opiedgfvi
    eqtri
    wph
    @24
    @31
    cI
    wph
    @23
    @30
    cF
    wph
    cN
    cz
    wcel
    #
    @23
    @30
    wceq
    wph
    cN
    eupth2.n
    nn0zd
    @32
    @30
    @23
    cc0
    cN
    fzval3
    eqcomd
    syl
    imaeq2d
    reseq2d
    syl5eq
    eupth2.o
    wph
    @9
    vk
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @33
    cP
    cfv
    #
    @33
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vk
    @8
    wral
    #
    @1
    cN
    cP
    cfv
    #
    @7
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    @13
    wph
    cG
    cupgr
    wcel
    @11
    @41
    eupth2.g
    wph
    @10
    @11
    eupth2.p
    @12
    syl
    cP
    vk
    cF
    cG
    cI
    eupth2.i
    upgrwlkedg
    syl2anc
    @40
    @45
    vk
    cN
    @8
    @33
    cN
    wceq
    #
    @35
    @1
    @39
    @44
    @46
    @34
    @0
    cI
    @33
    cN
    cF
    fveq2
    fveq2d
    @46
    @36
    @42
    @38
    @43
    @33
    cN
    cP
    fveq2
    @46
    @37
    @7
    cP
    @33
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eqeq12d
    rspcv
    sylc
    eupth2lem3lem7
end
