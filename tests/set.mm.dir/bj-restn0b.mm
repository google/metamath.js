include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "crest.mm"
include "co.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "jca.mm"
include "anim1i.mm"
include "an32.mm"
include "sylib.mm"
include "bj-restn0.mm"
include "imp.mm"
include "syl.mm"

theorem bj-restn0b
  let cA: class A
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( X e. ( V \ { (/) } ) /\ A e. W ) -> ( X |`t A ) =/= (/) )

  proof
    cX
    cV
    c0
    csn
    #
    cdif
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    #
    @2
    wa
    #
    cX
    c0
    wne
    #
    wa
    #
    cX
    cA
    crest
    co
    c0
    wne
    #
    @3
    @4
    @6
    wa
    #
    @2
    wa
    @7
    @1
    @9
    @2
    @1
    @4
    @6
    cX
    cV
    @0
    eldifi
    cX
    cV
    c0
    eldifsni
    jca
    anim1i
    @4
    @6
    @2
    an32
    sylib
    @5
    @6
    @8
    cA
    cV
    cW
    cX
    bj-restn0
    imp
    syl
end
