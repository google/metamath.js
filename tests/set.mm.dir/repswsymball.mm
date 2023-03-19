include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "creps.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wb.mm"
include "df-3an.mm"
include "a1i.mm"
include "cn0.mm"
include "lencl.mm"
include "anim2i.mm"
include "ancoms.mm"
include "repsdf2.mm"
include "syl.mm"
include "simpl.mm"
include "eqidd.mm"
include "jca.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "biimpd.mm"

theorem repswsymball
  let cS: class S
  let vi: setvar i
  let cV: class V
  let cW: class W

  disjoint S i
  disjoint W i
  assert |- ( ( W e. Word V /\ S e. V ) -> ( W = ( S repeatS ( # ` W ) ) -> A. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) = S ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    cW
    cS
    cW
    chash
    cfv
    #
    creps
    co
    wceq
    #
    vi
    cv
    cW
    cfv
    cS
    wceq
    vi
    cc0
    @3
    cfzo
    co
    wral
    #
    @2
    @0
    @3
    @3
    wceq
    #
    @5
    w3a
    #
    @0
    @6
    wa
    #
    @5
    wa
    #
    @4
    @5
    @7
    @9
    wb
    @2
    @0
    @6
    @5
    df-3an
    a1i
    @2
    @1
    @3
    cn0
    wcel
    #
    wa
    #
    @4
    @7
    wb
    @1
    @0
    @11
    @0
    @10
    @1
    cV
    cW
    lencl
    anim2i
    ancoms
    cS
    vi
    @3
    cV
    cW
    repsdf2
    syl
    @2
    @8
    @5
    @2
    @0
    @6
    @0
    @1
    simpl
    @2
    @3
    eqidd
    jca
    biantrurd
    3bitr4d
    biimpd
end
