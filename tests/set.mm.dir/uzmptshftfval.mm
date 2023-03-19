include "cshi.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wfn.mm"
include "wceq.mm"
include "cmin.mm"
include "wcel.mm"
include "cc.mm"
include "crab.mm"
include "fnmpti.mm"
include "zcnd.mm"
include "cvv.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "shftfn.mm"
include "sylancr.mm"
include "caddc.mm"
include "cz.mm"
include "shftuz.mm"
include "syl2anc.mm"
include "eleq2i.mm"
include "rabbii.mm"
include "3eqtr4g.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "dffn5.mm"
include "sylib.mm"
include "wa.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zsscn.mm"
include "sstri.mm"
include "sseli.mm"
include "shftval.mm"
include "syl2an.mm"
include "jca.mm"
include "eluzsub.mm"
include "3expa.mm"
include "sylan.mm"
include "sylan2b.mm"
include "syl6eleqr.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"

theorem uzmptshftfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  assume uzmptshftfval.f: |- F = ( x e. Z |-> B )
  assume uzmptshftfval.b: |- B e. _V
  assume uzmptshftfval.c: |- ( x = ( y - N ) -> B = C )
  assume uzmptshftfval.z: |- Z = ( ZZ>= ` M )
  assume uzmptshftfval.w: |- W = ( ZZ>= ` ( M + N ) )
  assume uzmptshftfval.m: |- ( ph -> M e. ZZ )
  assume uzmptshftfval.n: |- ( ph -> N e. ZZ )

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint Z x
  disjoint Z y
  disjoint ph y
  disjoint C x
  disjoint F y
  disjoint M y
  disjoint W y
  assert |- ( ph -> ( F shift N ) = ( y e. W |-> C ) )

  proof
    wph
    cF
    cN
    cshi
    co
    #
    vy
    cW
    vy
    cv
    #
    @0
    cfv
    #
    cmpt
    #
    vy
    cW
    cC
    cmpt
    wph
    @0
    cW
    wfn
    #
    @0
    @3
    wceq
    wph
    @0
    @1
    cN
    cmin
    co
    #
    cZ
    wcel
    #
    vy
    cc
    crab
    #
    wfn
    #
    @4
    wph
    cF
    cZ
    wfn
    cN
    cc
    wcel
    #
    @8
    vx
    cZ
    cB
    cF
    uzmptshftfval.b
    uzmptshftfval.f
    fnmpti
    wph
    cN
    uzmptshftfval.n
    zcnd
    #
    vy
    cN
    cZ
    cF
    cF
    vx
    cZ
    cB
    cmpt
    cvv
    uzmptshftfval.f
    vx
    cZ
    cB
    cZ
    cM
    cuz
    cfv
    #
    cvv
    uzmptshftfval.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    eqeltri
    #
    shftfn
    sylancr
    wph
    @7
    cW
    @0
    wph
    @5
    @11
    wcel
    #
    vy
    cc
    crab
    #
    cM
    cN
    caddc
    co
    #
    cuz
    cfv
    #
    @7
    cW
    wph
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @14
    @16
    wceq
    uzmptshftfval.n
    uzmptshftfval.m
    vy
    cN
    cM
    shftuz
    syl2anc
    @6
    @13
    vy
    cc
    cZ
    @11
    @5
    uzmptshftfval.z
    eleq2i
    rabbii
    uzmptshftfval.w
    3eqtr4g
    fneq2d
    mpbid
    vy
    cW
    @0
    dffn5
    sylib
    wph
    vy
    cW
    @2
    cC
    wph
    @1
    cW
    wcel
    #
    wa
    #
    @2
    @5
    cF
    cfv
    #
    cC
    wph
    @9
    @1
    cc
    wcel
    @2
    @21
    wceq
    @19
    @10
    cW
    cc
    @1
    cW
    cz
    cc
    cW
    @16
    cz
    uzmptshftfval.w
    @15
    uzssz
    eqsstri
    zsscn
    sstri
    sseli
    cN
    @1
    cF
    @12
    shftval
    syl2an
    @20
    @6
    @21
    cC
    wceq
    @20
    @5
    @11
    cZ
    @19
    wph
    @1
    @16
    wcel
    #
    @13
    cW
    @16
    @1
    uzmptshftfval.w
    eleq2i
    wph
    @18
    @17
    wa
    @22
    @13
    wph
    @18
    @17
    uzmptshftfval.m
    uzmptshftfval.n
    jca
    @18
    @17
    @22
    @13
    cN
    cM
    @1
    eluzsub
    3expa
    sylan
    sylan2b
    uzmptshftfval.z
    syl6eleqr
    vx
    @5
    cB
    cC
    cZ
    cF
    uzmptshftfval.c
    uzmptshftfval.f
    uzmptshftfval.b
    fvmpt3i
    syl
    eqtrd
    mpteq2dva
    eqtrd
end
