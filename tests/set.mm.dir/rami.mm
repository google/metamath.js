include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "wral.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "cram.mm"
include "wi.mm"
include "wal.mm"
include "cn0.mm"
include "crab.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "ramtcl2.mm"
include "ramtcl.mm"
include "bitr4d.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "albidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "pweq.mm"
include "rexeqdv.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl3c.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem rami
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cS: class S
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let cN: class N
  assume rami.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume rami.m: |- ( ph -> M e. NN0 )
  assume rami.r: |- ( ph -> R e. V )
  assume rami.f: |- ( ph -> F : R --> NN0 )
  assume rami.x: |- ( ph -> ( M Ramsey F ) e. NN0 )
  assume rami.s: |- ( ph -> S e. W )
  assume rami.l: |- ( ph -> ( M Ramsey F ) <_ ( # ` S ) )
  assume rami.g: |- ( ph -> G : ( S C M ) --> R )

  disjoint c x
  disjoint C c
  disjoint C x
  disjoint G c
  disjoint G x
  disjoint c ph
  disjoint ph x
  disjoint S c
  disjoint S x
  disjoint F c
  disjoint F x
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
  disjoint R c
  disjoint R x
  disjoint V c
  disjoint V x
  disjoint c f
  disjoint c g
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint f g
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint C f
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint C g
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint C n
  disjoint s t
  disjoint s x
  disjoint C s
  disjoint t x
  disjoint C t
  disjoint G f
  disjoint f ph
  disjoint g ph
  disjoint ph s
  disjoint ph t
  disjoint S f
  disjoint S s
  disjoint F f
  disjoint F g
  disjoint F n
  disjoint F s
  disjoint F t
  disjoint a f
  disjoint a g
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint b f
  disjoint b g
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint f i
  disjoint M f
  disjoint g i
  disjoint M g
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint M n
  disjoint M s
  disjoint M t
  disjoint R f
  disjoint R g
  disjoint R n
  disjoint R s
  disjoint R t
  disjoint N a
  disjoint N c
  disjoint N f
  disjoint N g
  disjoint N i
  disjoint N n
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint V f
  disjoint V g
  disjoint V n
  disjoint V s
  disjoint V t
  assert |- ( ph -> E. c e. R E. x e. ~P S ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' G " { c } ) ) )

  proof
    wph
    cG
    cR
    cS
    cM
    cC
    co
    #
    cmap
    co
    #
    wcel
    #
    vc
    cv
    #
    cF
    cfv
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    #
    @4
    cM
    cC
    co
    #
    vf
    cv
    #
    ccnv
    #
    @3
    csn
    #
    cima
    #
    wss
    #
    wa
    #
    vx
    cS
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    #
    vf
    @1
    wral
    #
    @5
    @6
    cG
    ccnv
    #
    @9
    cima
    #
    wss
    #
    wa
    #
    vx
    @13
    wrex
    vc
    cR
    wrex
    #
    wph
    @2
    @0
    cR
    cG
    wf
    #
    rami.g
    wph
    cR
    cV
    wcel
    #
    @0
    cvv
    wcel
    @2
    @22
    wb
    rami.r
    cS
    cM
    cC
    ovex
    cR
    @0
    cG
    cV
    cvv
    elmapg
    sylancl
    mpbird
    wph
    cS
    cW
    wcel
    cM
    cF
    cram
    co
    #
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @12
    vx
    @25
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    #
    vf
    cR
    @25
    cM
    cC
    co
    #
    cmap
    co
    #
    wral
    #
    wi
    #
    vs
    wal
    #
    @24
    cS
    chash
    cfv
    #
    cle
    wbr
    #
    @16
    rami.s
    wph
    @24
    vn
    cv
    #
    @26
    cle
    wbr
    #
    @33
    wi
    #
    vs
    wal
    #
    vn
    cn0
    crab
    #
    wcel
    #
    @35
    wph
    @24
    cn0
    wcel
    #
    @43
    rami.x
    wph
    cM
    cn0
    wcel
    #
    @23
    cR
    cn0
    cF
    wf
    #
    @44
    @43
    wb
    rami.m
    rami.r
    rami.f
    @45
    @23
    @46
    w3a
    @44
    @42
    c0
    wne
    @43
    vx
    cC
    cR
    @42
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    rami.c
    @42
    eqid
    #
    ramtcl2
    vx
    cC
    cR
    @42
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    rami.c
    @47
    ramtcl
    bitr4d
    syl3anc
    mpbid
    @43
    @44
    @35
    @41
    @35
    vn
    @24
    cn0
    @38
    @24
    wceq
    #
    @40
    @34
    vs
    @48
    @39
    @27
    @33
    @38
    @24
    @26
    cle
    breq1
    imbi1d
    albidv
    elrab
    simprbi
    syl
    rami.l
    @34
    @37
    @16
    wi
    vs
    cS
    cW
    @25
    cS
    wceq
    #
    @27
    @37
    @33
    @16
    @49
    @26
    @36
    @24
    cle
    @25
    cS
    chash
    fveq2
    breq2d
    @49
    @30
    @15
    vf
    @32
    @1
    @49
    @31
    @0
    cR
    cmap
    @25
    cS
    cM
    cC
    oveq1
    oveq2d
    @49
    @29
    @14
    vc
    cR
    @49
    @12
    vx
    @28
    @13
    @25
    cS
    pweq
    rexeqdv
    rexbidv
    raleqbidv
    imbi12d
    spcgv
    syl3c
    @15
    @21
    vf
    cG
    @1
    @7
    cG
    wceq
    #
    @12
    @20
    vc
    vx
    cR
    @13
    @50
    @11
    @19
    @5
    @50
    @10
    @18
    @6
    @50
    @8
    @17
    @9
    @7
    cG
    cnveq
    imaeq1d
    sseq2d
    anbi2d
    2rexbidv
    rspcv
    sylc
end
