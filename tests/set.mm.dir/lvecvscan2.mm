include "co.mm"
include "csg.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "neneqd.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "syl.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "lmodfgrp.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "lvecvs0or.mm"
include "lmodsubdir.mm"
include "eqeq1d.mm"
include "3bitr2rd.mm"
include "lmodvscl.mm"
include "lmodsubeq0.mm"
include "grpsubeq0.mm"
include "3bitr3d.mm"

theorem lvecvscan2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lvecmulcan2.v: |- V = ( Base ` W )
  assume lvecmulcan2.s: |- .x. = ( .s ` W )
  assume lvecmulcan2.f: |- F = ( Scalar ` W )
  assume lvecmulcan2.k: |- K = ( Base ` F )
  assume lvecmulcan2.o: |- .0. = ( 0g ` W )
  assume lvecmulcan2.w: |- ( ph -> W e. LVec )
  assume lvecmulcan2.a: |- ( ph -> A e. K )
  assume lvecmulcan2.b: |- ( ph -> B e. K )
  assume lvecmulcan2.x: |- ( ph -> X e. V )
  assume lvecmulcan2.n: |- ( ph -> X =/= .0. )


  assert |- ( ph -> ( ( A .x. X ) = ( B .x. X ) <-> A = B ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    cB
    cX
    c.x
    co
    #
    cW
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    cA
    cB
    cF
    csg
    cfv
    #
    co
    #
    cF
    c0g
    cfv
    #
    wceq
    #
    @0
    @1
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    @8
    @8
    cX
    c.0
    wceq
    #
    wo
    #
    @6
    cX
    c.x
    co
    #
    c.0
    wceq
    @4
    wph
    @11
    wn
    #
    @8
    @12
    wb
    wph
    cX
    c.0
    lvecmulcan2.n
    neneqd
    @14
    @8
    @11
    @8
    wo
    @12
    @11
    @8
    biorf
    @11
    @8
    orcom
    syl6bb
    syl
    wph
    @6
    c.x
    cF
    cK
    @7
    cV
    cW
    cX
    c.0
    lvecmulcan2.v
    lvecmulcan2.s
    lvecmulcan2.f
    lvecmulcan2.k
    @7
    eqid
    #
    lvecmulcan2.o
    lvecmulcan2.w
    wph
    cF
    cgrp
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    @6
    cK
    wcel
    wph
    cW
    clmod
    wcel
    #
    @16
    wph
    cW
    clvec
    wcel
    @19
    lvecmulcan2.w
    cW
    lveclmod
    syl
    #
    cF
    cW
    lvecmulcan2.f
    lmodfgrp
    syl
    #
    lvecmulcan2.a
    lvecmulcan2.b
    cK
    cF
    @5
    cA
    cB
    lvecmulcan2.k
    @5
    eqid
    #
    grpsubcl
    syl3anc
    lvecmulcan2.x
    lvecvs0or
    wph
    @13
    @3
    c.0
    wph
    cA
    cB
    @5
    c.x
    cF
    cK
    @2
    cV
    cW
    cX
    lvecmulcan2.v
    lvecmulcan2.s
    lvecmulcan2.f
    lvecmulcan2.k
    @2
    eqid
    #
    @22
    @20
    lvecmulcan2.a
    lvecmulcan2.b
    lvecmulcan2.x
    lmodsubdir
    eqeq1d
    3bitr2rd
    wph
    @19
    @0
    cV
    wcel
    #
    @1
    cV
    wcel
    #
    @4
    @9
    wb
    @20
    wph
    @19
    @17
    cX
    cV
    wcel
    #
    @24
    @20
    lvecmulcan2.a
    lvecmulcan2.x
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    lvecmulcan2.v
    lvecmulcan2.f
    lvecmulcan2.s
    lvecmulcan2.k
    lmodvscl
    syl3anc
    wph
    @19
    @18
    @26
    @25
    @20
    lvecmulcan2.b
    lvecmulcan2.x
    cB
    c.x
    cF
    cK
    cV
    cW
    cX
    lvecmulcan2.v
    lvecmulcan2.f
    lvecmulcan2.s
    lvecmulcan2.k
    lmodvscl
    syl3anc
    @0
    @1
    @2
    cV
    cW
    c.0
    lvecmulcan2.v
    lvecmulcan2.o
    @23
    lmodsubeq0
    syl3anc
    wph
    @16
    @17
    @18
    @8
    @10
    wb
    @21
    lvecmulcan2.a
    lvecmulcan2.b
    cK
    cF
    @5
    cA
    cB
    @7
    lvecmulcan2.k
    @15
    @22
    grpsubeq0
    syl3anc
    3bitr3d
end
