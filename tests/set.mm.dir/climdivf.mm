include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cli.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "simpr.mm"
include "cc0.mm"
include "csn.mm"
include "eldifad.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "reccld.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "climrecf.mm"
include "eqeltrd.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "climmulf.mm"
include "wbr.mm"
include "climcl.mm"
include "breqtrrd.mm"

theorem climdivf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume climdivf.1: |- F/ k ph
  assume climdivf.2: |- F/_ k F
  assume climdivf.3: |- F/_ k G
  assume climdivf.4: |- F/_ k H
  assume climdivf.5: |- Z = ( ZZ>= ` M )
  assume climdivf.6: |- ( ph -> M e. ZZ )
  assume climdivf.7: |- ( ph -> F ~~> A )
  assume climdivf.8: |- ( ph -> H e. X )
  assume climdivf.9: |- ( ph -> G ~~> B )
  assume climdivf.10: |- ( ph -> B =/= 0 )
  assume climdivf.11: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climdivf.12: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. ( CC \ { 0 } ) )
  assume climdivf.13: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) / ( G ` k ) ) )

  disjoint Z k
  assert |- ( ph -> H ~~> ( A / B ) )

  proof
    wph
    cH
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    cA
    cB
    cdiv
    co
    cli
    wph
    cA
    @0
    vk
    cF
    vk
    cZ
    c1
    vk
    cv
    #
    cG
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cH
    cM
    cX
    cZ
    climdivf.1
    climdivf.2
    vk
    cZ
    @3
    nfmpt1
    #
    climdivf.4
    climdivf.5
    climdivf.6
    climdivf.7
    climdivf.8
    wph
    cB
    vk
    cG
    @4
    cM
    cvv
    cZ
    climdivf.1
    climdivf.3
    @5
    climdivf.5
    climdivf.6
    climdivf.9
    climdivf.10
    climdivf.12
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @6
    @3
    cc
    wcel
    @1
    @4
    cfv
    #
    @3
    wceq
    wph
    @6
    simpr
    @7
    @2
    @7
    @2
    cc
    cc0
    csn
    #
    climdivf.12
    eldifad
    #
    @7
    @2
    cc
    @9
    cdif
    wcel
    @2
    cc0
    wne
    climdivf.12
    @2
    cc
    cc0
    eldifsni
    syl
    #
    reccld
    #
    vk
    cZ
    @3
    cc
    @4
    @4
    eqid
    fvmpt2
    syl2anc
    #
    @4
    cvv
    wcel
    wph
    vk
    cZ
    @3
    cZ
    cM
    cuz
    cfv
    cvv
    climdivf.5
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    climrecf
    climdivf.11
    @7
    @8
    @3
    cc
    @13
    @12
    eqeltrd
    @7
    @1
    cH
    cfv
    @1
    cF
    cfv
    #
    @2
    cdiv
    co
    @14
    @3
    cmul
    co
    @14
    @8
    cmul
    co
    climdivf.13
    @7
    @14
    @2
    climdivf.11
    @10
    @11
    divrecd
    @7
    @3
    @8
    @14
    cmul
    @7
    @8
    @3
    @13
    eqcomd
    oveq2d
    3eqtrd
    climmulf
    wph
    cA
    cB
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    climdivf.7
    cA
    cF
    climcl
    syl
    wph
    cG
    cB
    cli
    wbr
    cB
    cc
    wcel
    climdivf.9
    cB
    cG
    climcl
    syl
    climdivf.10
    divrecd
    breqtrrd
end
