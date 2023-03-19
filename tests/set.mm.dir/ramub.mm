include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "cmap.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "cram.mm"
include "elmapi.mm"
include "ancom2s.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimdva.mm"
include "alrimiv.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "albidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "ramtub.mm"
include "syl31anc.mm"

theorem ramub
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  let vn: setvar n
  let vt: setvar t
  let cG: class G
  let cS: class S
  assume rami.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume rami.m: |- ( ph -> M e. NN0 )
  assume rami.r: |- ( ph -> R e. V )
  assume rami.f: |- ( ph -> F : R --> NN0 )
  assume ramub.n: |- ( ph -> N e. NN0 )
  assume ramub.i: |- ( ( ph /\ ( N <_ ( # ` s ) /\ f : ( s C M ) --> R ) ) -> E. c e. R E. x e. ~P s ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' f " { c } ) ) )

  disjoint c f
  disjoint c s
  disjoint c x
  disjoint C c
  disjoint f s
  disjoint f x
  disjoint C f
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint c ph
  disjoint f ph
  disjoint ph s
  disjoint ph x
  disjoint F c
  disjoint F f
  disjoint F s
  disjoint F x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a s
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b i
  disjoint b s
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i s
  disjoint i x
  disjoint M i
  disjoint M s
  disjoint M x
  disjoint R c
  disjoint R f
  disjoint R s
  disjoint R x
  disjoint N a
  disjoint N c
  disjoint N f
  disjoint N i
  disjoint N s
  disjoint N x
  disjoint V c
  disjoint V f
  disjoint V s
  disjoint V x
  disjoint c g
  disjoint c n
  disjoint c t
  disjoint f g
  disjoint f n
  disjoint f t
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
  disjoint t x
  disjoint C t
  disjoint G c
  disjoint G f
  disjoint G x
  disjoint g ph
  disjoint ph t
  disjoint S c
  disjoint S f
  disjoint S s
  disjoint S x
  disjoint F g
  disjoint F n
  disjoint F t
  disjoint a g
  disjoint a n
  disjoint a t
  disjoint b g
  disjoint b n
  disjoint b t
  disjoint g i
  disjoint M g
  disjoint i n
  disjoint i t
  disjoint M n
  disjoint M t
  disjoint R g
  disjoint R n
  disjoint R t
  disjoint N g
  disjoint N n
  disjoint N t
  disjoint V g
  disjoint V n
  disjoint V t
  assert |- ( ph -> ( M Ramsey F ) <_ N )

  proof
    wph
    cM
    cn0
    wcel
    cR
    cV
    wcel
    cR
    cn0
    cF
    wf
    cN
    vn
    cv
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
    @5
    cM
    cC
    co
    vf
    cv
    #
    ccnv
    @4
    csn
    cima
    wss
    wa
    vx
    @1
    cpw
    wrex
    vc
    cR
    wrex
    #
    vf
    cR
    @1
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
    vn
    cn0
    crab
    #
    wcel
    #
    cM
    cF
    cram
    co
    cN
    cle
    wbr
    rami.m
    rami.r
    rami.f
    wph
    cN
    cn0
    wcel
    cN
    @2
    cle
    wbr
    #
    @10
    wi
    #
    vs
    wal
    #
    @14
    ramub.n
    wph
    @16
    vs
    wph
    @15
    @7
    vf
    @9
    @6
    @9
    wcel
    wph
    @8
    cR
    @6
    wf
    #
    @15
    @7
    wi
    @6
    cR
    @8
    elmapi
    wph
    @18
    @15
    @7
    wph
    @15
    @18
    @7
    ramub.i
    ancom2s
    expr
    sylan2
    ralrimdva
    alrimiv
    @12
    @17
    vn
    cN
    cn0
    @0
    cN
    wceq
    #
    @11
    @16
    vs
    @19
    @3
    @15
    @10
    @0
    cN
    @2
    cle
    breq1
    imbi1d
    albidv
    elrab
    sylanbrc
    vx
    cN
    cC
    cR
    @13
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
    @13
    eqid
    ramtub
    syl31anc
end
