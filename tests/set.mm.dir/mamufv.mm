include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "mamuval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem mamufv
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vj: setvar j
  let cF: class F
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vp: setvar p
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mamufval.f: |- F = ( R maMul <. M , N , P >. )
  assume mamufval.b: |- B = ( Base ` R )
  assume mamufval.t: |- .x. = ( .r ` R )
  assume mamufval.r: |- ( ph -> R e. V )
  assume mamufval.m: |- ( ph -> M e. Fin )
  assume mamufval.n: |- ( ph -> N e. Fin )
  assume mamufval.p: |- ( ph -> P e. Fin )
  assume mamuval.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mamuval.y: |- ( ph -> Y e. ( B ^m ( N X. P ) ) )
  assume mamufv.i: |- ( ph -> I e. M )
  assume mamufv.k: |- ( ph -> K e. P )

  disjoint M j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint X j
  disjoint Y j
  disjoint j ph
  disjoint I j
  disjoint K j
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i o
  disjoint i p
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint j k
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
  disjoint M i
  disjoint M k
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N i
  disjoint N k
  disjoint N o
  disjoint N r
  disjoint N x
  disjoint N y
  disjoint P i
  disjoint P k
  disjoint P o
  disjoint P r
  disjoint P x
  disjoint P y
  disjoint R i
  disjoint R k
  disjoint R o
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint X i
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Y i
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint i ph
  disjoint k ph
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
  disjoint .x. i
  disjoint .x. k
  disjoint I i
  disjoint I k
  disjoint K i
  disjoint K k
  assert |- ( ph -> ( I ( X F Y ) K ) = ( R gsum ( j e. N |-> ( ( I X j ) .x. ( j Y K ) ) ) ) )

  proof
    wph
    vi
    vk
    cI
    cK
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
    cX
    co
    #
    @1
    vk
    cv
    #
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
    cR
    vj
    cN
    cI
    @1
    cX
    co
    #
    @1
    cK
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
    cX
    cY
    cF
    co
    cvv
    wph
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
    cX
    cY
    mamufval.f
    mamufval.b
    mamufval.t
    mamufval.r
    mamufval.m
    mamufval.n
    mamufval.p
    mamuval.x
    mamuval.y
    mamuval
    wph
    @0
    cI
    wceq
    #
    @3
    cK
    wceq
    #
    wa
    #
    wa
    #
    @6
    @10
    cR
    cgsu
    @14
    vj
    cN
    @5
    @9
    @13
    @5
    @9
    wceq
    wph
    @11
    @12
    @2
    @7
    @4
    @8
    c.x
    @0
    cI
    @1
    cX
    oveq1
    @3
    cK
    @1
    cY
    oveq2
    oveqan12d
    adantl
    mpteq2dv
    oveq2d
    mamufv.i
    mamufv.k
    wph
    cR
    @10
    cgsu
    ovexd
    ovmpt2d
end
