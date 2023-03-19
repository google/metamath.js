include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cvv.mm"
include "mamufval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "mpt2eq3dv.mm"
include "cfn.mm"
include "wcel.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "ovmpt2d.mm"

theorem mamuval
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vp: setvar p
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cK: class K
  assume mamufval.f: |- F = ( R maMul <. M , N , P >. )
  assume mamufval.b: |- B = ( Base ` R )
  assume mamufval.t: |- .x. = ( .r ` R )
  assume mamufval.r: |- ( ph -> R e. V )
  assume mamufval.m: |- ( ph -> M e. Fin )
  assume mamufval.n: |- ( ph -> N e. Fin )
  assume mamufval.p: |- ( ph -> P e. Fin )
  assume mamuval.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mamuval.y: |- ( ph -> Y e. ( B ^m ( N X. P ) ) )

  disjoint i j
  disjoint i k
  disjoint j k
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint .x. i
  disjoint .x. k
  disjoint i m
  disjoint i n
  disjoint i o
  disjoint i p
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j p
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k n
  disjoint k o
  disjoint k p
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m o
  disjoint m p
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n o
  disjoint n p
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint o p
  disjoint o r
  disjoint o x
  disjoint o y
  disjoint p r
  disjoint p x
  disjoint p y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N o
  disjoint N r
  disjoint N x
  disjoint N y
  disjoint P o
  disjoint P r
  disjoint P x
  disjoint P y
  disjoint R o
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint o ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint B o
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint .x. o
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint K i
  disjoint K j
  disjoint K k
  assert |- ( ph -> ( X F Y ) = ( i e. M , k e. P |-> ( R gsum ( j e. N |-> ( ( i X j ) .x. ( j Y k ) ) ) ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cM
    cN
    cxp
    cmap
    co
    cB
    cN
    cP
    cxp
    cmap
    co
    vi
    vk
    cM
    cP
    cR
    vj
    cN
    vi
    cv
    #
    vj
    cv
    #
    vx
    cv
    #
    co
    #
    @1
    vk
    cv
    #
    vy
    cv
    #
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    vi
    vk
    cM
    cP
    cR
    vj
    cN
    @0
    @1
    cX
    co
    #
    @1
    @4
    cY
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cF
    cvv
    wph
    vx
    vy
    cB
    cP
    cR
    c.x
    vi
    vj
    vk
    cF
    cM
    cN
    cV
    mamufval.f
    mamufval.b
    mamufval.t
    mamufval.r
    mamufval.m
    mamufval.n
    mamufval.p
    mamufval
    wph
    @2
    cX
    wceq
    #
    @5
    cY
    wceq
    #
    wa
    #
    wa
    #
    vi
    vk
    cM
    cP
    @9
    @14
    @19
    @8
    @13
    cR
    cgsu
    @19
    vj
    cN
    @7
    @12
    @18
    @7
    @12
    wceq
    wph
    @16
    @17
    @3
    @10
    @6
    @11
    c.x
    @0
    @1
    @2
    cX
    oveq
    @1
    @4
    @5
    cY
    oveq
    oveqan12d
    adantl
    mpteq2dv
    oveq2d
    mpt2eq3dv
    mamuval.x
    mamuval.y
    wph
    cM
    cfn
    wcel
    cP
    cfn
    wcel
    @15
    cvv
    wcel
    mamufval.m
    mamufval.p
    vi
    vk
    cM
    cP
    @14
    cfn
    cfn
    mpt2exga
    syl2anc
    ovmpt2d
end
