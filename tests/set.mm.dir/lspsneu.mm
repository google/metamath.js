include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cdif.mm"
include "wreu.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "eldifad.mm"
include "lspsneq.mm"
include "biimpd.mm"
include "wcel.mm"
include "w3a.mm"
include "eqtr2.mm"
include "3ad2ant3.mm"
include "clvec.mm"
include "simp1l.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2r.mm"
include "wne.mm"
include "eldifsni.mm"
include "3syl.mm"
include "lvecvscan2.mm"
include "mpbid.mm"
include "3exp.mm"
include "ex.mm"
include "ralrimdvv.mm"
include "jcad.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "reu4.mm"
include "syl6ibr.mm"
include "reurex.mm"
include "syl5ibr.mm"
include "impbid.mm"
include "cbvreuv.mm"
include "syl6bb.mm"

theorem lspsneu
  let wph: wff ph
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume lspsneu.v: |- V = ( Base ` W )
  assume lspsneu.s: |- S = ( Scalar ` W )
  assume lspsneu.k: |- K = ( Base ` S )
  assume lspsneu.o: |- O = ( 0g ` S )
  assume lspsneu.t: |- .x. = ( .s ` W )
  assume lspsneu.z: |- .0. = ( 0g ` W )
  assume lspsneu.n: |- N = ( LSpan ` W )
  assume lspsneu.w: |- ( ph -> W e. LVec )
  assume lspsneu.x: |- ( ph -> X e. V )
  assume lspsneu.y: |- ( ph -> Y e. ( V \ { .0. } ) )

  disjoint K k
  disjoint O k
  disjoint .x. k
  disjoint X k
  disjoint Y k
  disjoint i j
  disjoint i k
  disjoint K i
  disjoint j k
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint O i
  disjoint O j
  disjoint .x. i
  disjoint .x. j
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> ( ( N ` { X } ) = ( N ` { Y } ) <-> E! k e. ( K \ { O } ) X = ( k .x. Y ) ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wceq
    #
    cX
    vj
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    vj
    cK
    cO
    csn
    #
    cdif
    #
    wreu
    #
    cX
    vk
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    vk
    @5
    wreu
    wph
    @0
    @6
    wph
    @0
    @3
    vj
    @5
    wrex
    #
    @3
    cX
    vi
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    wa
    #
    vj
    vi
    weq
    #
    wi
    #
    vi
    @5
    wral
    vj
    @5
    wral
    #
    wa
    @6
    wph
    @0
    @10
    @17
    wph
    @0
    @10
    wph
    cS
    c.x
    vj
    cK
    cN
    cV
    cW
    cX
    cY
    cO
    lspsneu.v
    lspsneu.s
    lspsneu.k
    lspsneu.o
    lspsneu.t
    lspsneu.n
    lspsneu.w
    lspsneu.x
    wph
    cY
    cV
    c.0
    csn
    #
    lspsneu.y
    eldifad
    #
    lspsneq
    #
    biimpd
    wph
    @0
    @16
    vj
    vi
    @5
    @5
    wph
    @0
    @1
    @5
    wcel
    #
    @11
    @5
    wcel
    #
    wa
    #
    @16
    wi
    wph
    @0
    wa
    #
    @23
    @14
    @15
    @24
    @23
    @14
    w3a
    #
    @2
    @12
    wceq
    #
    @15
    @14
    @24
    @26
    @23
    cX
    @2
    @12
    eqtr2
    3ad2ant3
    @25
    @1
    @11
    c.x
    cS
    cK
    cV
    cW
    cY
    c.0
    lspsneu.v
    lspsneu.t
    lspsneu.s
    lspsneu.k
    lspsneu.z
    @25
    wph
    cW
    clvec
    wcel
    wph
    @0
    @23
    @14
    simp1l
    #
    lspsneu.w
    syl
    @25
    @1
    cK
    @4
    @24
    @21
    @22
    @14
    simp2l
    eldifad
    @25
    @11
    cK
    @4
    @24
    @21
    @22
    @14
    simp2r
    eldifad
    @25
    wph
    cY
    cV
    wcel
    @27
    @19
    syl
    @25
    wph
    cY
    cV
    @18
    cdif
    wcel
    cY
    c.0
    wne
    @27
    lspsneu.y
    cY
    cV
    c.0
    eldifsni
    3syl
    lvecvscan2
    mpbid
    3exp
    ex
    ralrimdvv
    jcad
    @3
    @13
    vj
    vi
    @5
    @15
    @2
    @12
    cX
    @1
    @11
    cY
    c.x
    oveq1
    eqeq2d
    reu4
    syl6ibr
    @6
    @0
    wph
    @10
    @3
    vj
    @5
    reurex
    @20
    syl5ibr
    impbid
    @3
    @9
    vj
    vk
    @5
    vj
    vk
    weq
    @2
    @8
    cX
    @1
    @7
    cY
    c.x
    oveq1
    eqeq2d
    cbvreuv
    syl6bb
end
