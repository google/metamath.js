include "csg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wo.mm"
include "wne.mm"
include "wb.mm"
include "wn.mm"
include "df-ne.mm"
include "biorf.mm"
include "sylbi.mm"
include "syl.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "eqid.mm"
include "lmodsubeq0.mm"
include "syl3anc.mm"
include "lmodsubdi.mm"
include "eqeq1d.mm"
include "lmodvsubcl.mm"
include "lvecvs0or.mm"
include "lmodvscl.mm"
include "3bitr3d.mm"
include "3bitr3rd.mm"

theorem lvecvscan
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lvecmulcan.v: |- V = ( Base ` W )
  assume lvecmulcan.s: |- .x. = ( .s ` W )
  assume lvecmulcan.f: |- F = ( Scalar ` W )
  assume lvecmulcan.k: |- K = ( Base ` F )
  assume lvecmulcan.o: |- .0. = ( 0g ` F )
  assume lvecmulcan.w: |- ( ph -> W e. LVec )
  assume lvecmulcan.a: |- ( ph -> A e. K )
  assume lvecmulcan.x: |- ( ph -> X e. V )
  assume lvecmulcan.y: |- ( ph -> Y e. V )
  assume lvecmulcan.n: |- ( ph -> A =/= .0. )


  assert |- ( ph -> ( ( A .x. X ) = ( A .x. Y ) <-> X = Y ) )

  proof
    wph
    cX
    cY
    cW
    csg
    cfv
    #
    co
    #
    cW
    c0g
    cfv
    #
    wceq
    #
    cA
    c.0
    wceq
    #
    @3
    wo
    #
    cX
    cY
    wceq
    #
    cA
    cX
    c.x
    co
    #
    cA
    cY
    c.x
    co
    #
    wceq
    #
    wph
    cA
    c.0
    wne
    #
    @3
    @5
    wb
    #
    lvecmulcan.n
    @10
    @4
    wn
    @11
    cA
    c.0
    df-ne
    @4
    @3
    biorf
    sylbi
    syl
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @3
    @6
    wb
    wph
    cW
    clvec
    wcel
    @12
    lvecmulcan.w
    cW
    lveclmod
    syl
    #
    lvecmulcan.x
    lvecmulcan.y
    cX
    cY
    @0
    cV
    cW
    @2
    lvecmulcan.v
    @2
    eqid
    #
    @0
    eqid
    #
    lmodsubeq0
    syl3anc
    wph
    cA
    @1
    c.x
    co
    #
    @2
    wceq
    @7
    @8
    @0
    co
    #
    @2
    wceq
    #
    @5
    @9
    wph
    @18
    @19
    @2
    wph
    cA
    c.x
    cF
    cK
    @0
    cV
    cW
    cX
    cY
    lvecmulcan.v
    lvecmulcan.s
    lvecmulcan.f
    lvecmulcan.k
    @17
    @15
    lvecmulcan.a
    lvecmulcan.x
    lvecmulcan.y
    lmodsubdi
    eqeq1d
    wph
    cA
    c.x
    cF
    cK
    c.0
    cV
    cW
    @1
    @2
    lvecmulcan.v
    lvecmulcan.s
    lvecmulcan.f
    lvecmulcan.k
    lvecmulcan.o
    @16
    lvecmulcan.w
    lvecmulcan.a
    wph
    @12
    @13
    @14
    @1
    cV
    wcel
    @15
    lvecmulcan.x
    lvecmulcan.y
    @0
    cV
    cW
    cX
    cY
    lvecmulcan.v
    @17
    lmodvsubcl
    syl3anc
    lvecvs0or
    wph
    @12
    @7
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    @20
    @9
    wb
    @15
    wph
    @12
    cA
    cK
    wcel
    #
    @13
    @21
    @15
    lvecmulcan.a
    lvecmulcan.x
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    lvecmulcan.v
    lvecmulcan.f
    lvecmulcan.s
    lvecmulcan.k
    lmodvscl
    syl3anc
    wph
    @12
    @23
    @14
    @22
    @15
    lvecmulcan.a
    lvecmulcan.y
    cA
    c.x
    cF
    cK
    cV
    cW
    cY
    lvecmulcan.v
    lvecmulcan.f
    lvecmulcan.s
    lvecmulcan.k
    lmodvscl
    syl3anc
    @7
    @8
    @0
    cV
    cW
    @2
    lvecmulcan.v
    @16
    @17
    lmodsubeq0
    syl3anc
    3bitr3d
    3bitr3rd
end
