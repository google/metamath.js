include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "nfov.mm"
include "nfeq.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "climrec.mm"

theorem climrecf
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climrecf.1: |- F/ k ph
  assume climrecf.2: |- F/_ k G
  assume climrecf.3: |- F/_ k H
  assume climrecf.4: |- Z = ( ZZ>= ` M )
  assume climrecf.5: |- ( ph -> M e. ZZ )
  assume climrecf.6: |- ( ph -> G ~~> A )
  assume climrecf.7: |- ( ph -> A =/= 0 )
  assume climrecf.8: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. ( CC \ { 0 } ) )
  assume climrecf.9: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( 1 / ( G ` k ) ) )
  assume climrecf.10: |- ( ph -> H e. W )

  disjoint Z k
  disjoint j k
  disjoint j ph
  disjoint A j
  disjoint G j
  disjoint H j
  disjoint Z j
  assert |- ( ph -> H ~~> ( 1 / A ) )

  proof
    wph
    cA
    vj
    cG
    cH
    cM
    cW
    cZ
    climrecf.4
    climrecf.5
    climrecf.6
    climrecf.7
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @0
    cG
    cfv
    #
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @6
    cG
    cfv
    #
    @4
    wcel
    #
    wi
    vk
    vj
    @8
    @10
    vk
    wph
    @7
    vk
    climrecf.1
    @7
    vk
    nfv
    nfan
    #
    vk
    @9
    @4
    vk
    @6
    cG
    climrecf.2
    vk
    @6
    nfcv
    #
    nffv
    #
    nfel1
    nfim
    @0
    @6
    wceq
    #
    @2
    @8
    @5
    @10
    @14
    @1
    @7
    wph
    @0
    @6
    cZ
    eleq1
    anbi2d
    #
    @14
    @3
    @9
    @4
    @0
    @6
    cG
    fveq2
    #
    eleq1d
    imbi12d
    climrecf.8
    chvar
    @2
    @0
    cH
    cfv
    #
    c1
    @3
    cdiv
    co
    #
    wceq
    #
    wi
    @8
    @6
    cH
    cfv
    #
    c1
    @9
    cdiv
    co
    #
    wceq
    #
    wi
    vk
    vj
    @8
    @22
    vk
    @11
    vk
    @20
    @21
    vk
    @6
    cH
    climrecf.3
    @12
    nffv
    vk
    c1
    @9
    cdiv
    vk
    c1
    nfcv
    vk
    cdiv
    nfcv
    @13
    nfov
    nfeq
    nfim
    @14
    @2
    @8
    @19
    @22
    @15
    @14
    @17
    @20
    @18
    @21
    @0
    @6
    cH
    fveq2
    @14
    @3
    @9
    c1
    cdiv
    @16
    oveq2d
    eqeq12d
    imbi12d
    climrecf.9
    chvar
    climrecf.10
    climrec
end
