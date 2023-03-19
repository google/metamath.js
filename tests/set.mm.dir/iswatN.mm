include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "cpolN.mm"
include "cdif.mm"
include "wn.mm"
include "watvalN.mm"
include "eleq2d.mm"
include "eldif.mm"
include "syl6bb.mm"

theorem iswatN
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cK: class K
  let cW: class W
  let vd: setvar d
  let vk: setvar k
  assume watomfval.a: |- A = ( Atoms ` K )
  assume watomfval.p: |- P = ( _|_P ` K )
  assume watomfval.w: |- W = ( WAtoms ` K )


  assert |- ( ( K e. B /\ D e. A ) -> ( P e. ( W ` D ) <-> ( P e. A /\ -. P e. ( ( _|_P ` K ) ` { D } ) ) ) )

  proof
    cK
    cB
    wcel
    cD
    cA
    wcel
    wa
    #
    cP
    cD
    cW
    cfv
    #
    wcel
    cP
    cA
    cD
    csn
    cK
    cpolN
    cfv
    cfv
    #
    cdif
    #
    wcel
    cP
    cA
    wcel
    cP
    @2
    wcel
    wn
    wa
    @0
    @1
    @3
    cP
    cA
    cB
    cD
    cP
    cK
    cW
    watomfval.a
    watomfval.p
    watomfval.w
    watvalN
    eleq2d
    cP
    cA
    @2
    eldif
    syl6bb
end
