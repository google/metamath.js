include "cram.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "chash.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "c1.mm"
include "cfz.mm"
include "cpw.mm"
include "wrex.mm"
include "cfn.mm"
include "cn0.mm"
include "wcel.mm"
include "adantr.mm"
include "wf.mm"
include "simpr.mm"
include "ramubcl.mm"
include "syl32anc.mm"
include "fzfid.mm"
include "wceq.mm"
include "hashfz1.mm"
include "syl.mm"
include "breq2d.mm"
include "biimpar.mm"
include "rami.mm"
include "wi.mm"
include "elpwi.mm"
include "adantlr.mm"
include "simprr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "nn0red.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ltnled.mm"
include "sylibd.mm"
include "sylanr2.mm"
include "con2d.mm"
include "imnan.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "pm2.01da.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "ramxrcl.mm"
include "syl3anc.mm"
include "xrltnle.mm"
include "mpbird.mm"

theorem ramlb
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume ramlb.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume ramlb.m: |- ( ph -> M e. NN0 )
  assume ramlb.r: |- ( ph -> R e. V )
  assume ramlb.f: |- ( ph -> F : R --> NN0 )
  assume ramlb.s: |- ( ph -> N e. NN0 )
  assume ramlb.g: |- ( ph -> G : ( ( 1 ... N ) C M ) --> R )
  assume ramlb.i: |- ( ( ph /\ ( c e. R /\ x C_ ( 1 ... N ) ) ) -> ( ( x C M ) C_ ( `' G " { c } ) -> ( # ` x ) < ( F ` c ) ) )

  disjoint c x
  disjoint C c
  disjoint C x
  disjoint F c
  disjoint F x
  disjoint G c
  disjoint G x
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b i
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint i x
  disjoint M i
  disjoint M x
  disjoint c ph
  disjoint ph x
  disjoint N c
  disjoint N x
  disjoint R c
  disjoint R x
  disjoint V c
  disjoint V x
  assert |- ( ph -> N < ( M Ramsey F ) )

  proof
    wph
    cN
    cM
    cF
    cram
    co
    #
    clt
    wbr
    #
    @0
    cN
    cle
    wbr
    #
    wn
    #
    wph
    @2
    wph
    @2
    wa
    #
    vc
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @7
    cM
    cC
    co
    cG
    ccnv
    @5
    csn
    cima
    wss
    #
    wa
    #
    vx
    c1
    cN
    cfz
    co
    #
    cpw
    #
    wrex
    vc
    cR
    wrex
    @3
    @4
    vx
    cC
    cR
    @12
    vi
    cF
    cG
    cM
    cV
    cfn
    va
    vb
    vc
    ramlb.c
    wph
    cM
    cn0
    wcel
    #
    @2
    ramlb.m
    adantr
    #
    wph
    cR
    cV
    wcel
    #
    @2
    ramlb.r
    adantr
    #
    wph
    cR
    cn0
    cF
    wf
    #
    @2
    ramlb.f
    adantr
    #
    @4
    @14
    @16
    @18
    cN
    cn0
    wcel
    #
    @2
    @0
    cn0
    wcel
    @15
    @17
    @19
    wph
    @20
    @2
    ramlb.s
    adantr
    wph
    @2
    simpr
    cN
    cR
    cF
    cM
    cV
    ramubcl
    syl32anc
    @4
    c1
    cN
    fzfid
    wph
    @0
    @12
    chash
    cfv
    #
    cle
    wbr
    @2
    wph
    @21
    cN
    @0
    cle
    wph
    @20
    @21
    cN
    wceq
    ramlb.s
    cN
    hashfz1
    syl
    breq2d
    biimpar
    wph
    @12
    cM
    cC
    co
    cR
    cG
    wf
    @2
    ramlb.g
    adantr
    rami
    @4
    @11
    @3
    vc
    vx
    cR
    @13
    @4
    @5
    cR
    wcel
    #
    @7
    @13
    wcel
    #
    wa
    wa
    #
    @11
    @3
    @24
    @9
    @10
    wn
    wi
    @11
    wn
    @24
    @10
    @9
    @23
    @4
    @22
    @7
    @12
    wss
    #
    @10
    @9
    wn
    #
    wi
    @7
    @12
    elpwi
    @4
    @22
    @25
    wa
    #
    wa
    #
    @10
    @8
    @6
    clt
    wbr
    #
    @26
    wph
    @27
    @10
    @29
    wi
    @2
    ramlb.i
    adantlr
    @28
    @8
    @6
    @28
    @8
    @28
    @7
    cfn
    wcel
    #
    @8
    cn0
    wcel
    @28
    @12
    cfn
    wcel
    @25
    @30
    @28
    c1
    cN
    fzfid
    @4
    @22
    @25
    simprr
    @12
    @7
    ssfi
    syl2anc
    @7
    hashcl
    syl
    nn0red
    @28
    @6
    @4
    @18
    @22
    @6
    cn0
    wcel
    @27
    @19
    @22
    @25
    simpl
    cR
    cn0
    @5
    cF
    ffvelrn
    syl2an
    nn0red
    ltnled
    sylibd
    sylanr2
    con2d
    @9
    @10
    imnan
    sylib
    pm2.21d
    rexlimdvva
    mpd
    pm2.01da
    wph
    cN
    cxr
    wcel
    @0
    cxr
    wcel
    #
    @1
    @3
    wb
    wph
    cN
    wph
    cN
    ramlb.s
    nn0red
    rexrd
    wph
    @14
    @16
    @18
    @31
    ramlb.m
    ramlb.r
    ramlb.f
    cR
    cF
    cM
    cV
    ramxrcl
    syl3anc
    cN
    @0
    xrltnle
    syl2anc
    mpbird
end
