include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "oveq2.mm"
include "cmulr.mm"
include "cur.mm"
include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "clvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "csn.mm"
include "eldifad.mm"
include "cdif.mm"
include "eldifsni.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "clmod.mm"
include "lveclmod.mm"
include "drnginvrcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "sylan9eqr.mm"
include "drnginvrr.mm"
include "3eqtr3rd.mm"
include "sylan9eq.mm"
include "impbida.mm"
include "eqcom.mm"
include "syl6bb.mm"

theorem lvecinv
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lvecinv.v: |- V = ( Base ` W )
  assume lvecinv.t: |- .x. = ( .s ` W )
  assume lvecinv.f: |- F = ( Scalar ` W )
  assume lvecinv.k: |- K = ( Base ` F )
  assume lvecinv.o: |- .0. = ( 0g ` F )
  assume lvecinv.i: |- I = ( invr ` F )
  assume lvecinv.w: |- ( ph -> W e. LVec )
  assume lvecinv.a: |- ( ph -> A e. ( K \ { .0. } ) )
  assume lvecinv.x: |- ( ph -> X e. V )
  assume lvecinv.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( X = ( A .x. Y ) <-> Y = ( ( I ` A ) .x. X ) ) )

  proof
    wph
    cX
    cA
    cY
    c.x
    co
    #
    wceq
    #
    cA
    cI
    cfv
    #
    cX
    c.x
    co
    #
    cY
    wceq
    #
    cY
    @3
    wceq
    wph
    @1
    @4
    @1
    wph
    @3
    @2
    @0
    c.x
    co
    #
    cY
    cX
    @0
    @2
    c.x
    oveq2
    wph
    @2
    cA
    cF
    cmulr
    cfv
    #
    co
    #
    cY
    c.x
    co
    #
    cF
    cur
    cfv
    #
    cY
    c.x
    co
    #
    @5
    cY
    wph
    @7
    @9
    cY
    c.x
    wph
    cF
    cdr
    wcel
    #
    cA
    cK
    wcel
    #
    cA
    c.0
    wne
    #
    @7
    @9
    wceq
    wph
    cW
    clvec
    wcel
    #
    @11
    lvecinv.w
    cF
    cW
    lvecinv.f
    lvecdrng
    syl
    #
    wph
    cA
    cK
    c.0
    csn
    #
    lvecinv.a
    eldifad
    #
    wph
    cA
    cK
    @16
    cdif
    wcel
    @13
    lvecinv.a
    cA
    cK
    c.0
    eldifsni
    syl
    #
    cK
    cF
    @6
    @9
    cI
    cA
    c.0
    lvecinv.k
    lvecinv.o
    @6
    eqid
    #
    @9
    eqid
    #
    lvecinv.i
    drnginvrl
    syl3anc
    oveq1d
    wph
    cW
    clmod
    wcel
    #
    @2
    cK
    wcel
    #
    @12
    cY
    cV
    wcel
    #
    @8
    @5
    wceq
    wph
    @14
    @21
    lvecinv.w
    cW
    lveclmod
    syl
    #
    wph
    @11
    @12
    @13
    @22
    @15
    @17
    @18
    cK
    cF
    cI
    cA
    c.0
    lvecinv.k
    lvecinv.o
    lvecinv.i
    drnginvrcl
    syl3anc
    #
    @17
    lvecinv.y
    @2
    cA
    c.x
    @6
    cF
    cK
    cV
    cW
    cY
    lvecinv.v
    lvecinv.f
    lvecinv.t
    lvecinv.k
    @19
    lmodvsass
    syl13anc
    wph
    @21
    @23
    @10
    cY
    wceq
    @24
    lvecinv.y
    c.x
    @9
    cF
    cV
    cW
    cY
    lvecinv.v
    lvecinv.f
    lvecinv.t
    @20
    lmodvs1
    syl2anc
    3eqtr3d
    sylan9eqr
    wph
    @4
    cX
    cA
    @3
    c.x
    co
    #
    @0
    wph
    cA
    @2
    @6
    co
    #
    cX
    c.x
    co
    #
    @9
    cX
    c.x
    co
    #
    @26
    cX
    wph
    @27
    @9
    cX
    c.x
    wph
    @11
    @12
    @13
    @27
    @9
    wceq
    @15
    @17
    @18
    cK
    cF
    @6
    @9
    cI
    cA
    c.0
    lvecinv.k
    lvecinv.o
    @19
    @20
    lvecinv.i
    drnginvrr
    syl3anc
    oveq1d
    wph
    @21
    @12
    @22
    cX
    cV
    wcel
    #
    @28
    @26
    wceq
    @24
    @17
    @25
    lvecinv.x
    cA
    @2
    c.x
    @6
    cF
    cK
    cV
    cW
    cX
    lvecinv.v
    lvecinv.f
    lvecinv.t
    lvecinv.k
    @19
    lmodvsass
    syl13anc
    wph
    @21
    @30
    @29
    cX
    wceq
    @24
    lvecinv.x
    c.x
    @9
    cF
    cV
    cW
    cX
    lvecinv.v
    lvecinv.f
    lvecinv.t
    @20
    lmodvs1
    syl2anc
    3eqtr3rd
    @3
    cY
    cA
    c.x
    oveq2
    sylan9eq
    impbida
    @3
    cY
    eqcom
    syl6bb
end
