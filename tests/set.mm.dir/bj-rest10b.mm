include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "eldif.mm"
include "0ex.mm"
include "elsn2.mm"
include "neqne.mm"
include "sylnbi.mm"
include "anim2i.mm"
include "sylbi.mm"
include "bj-rest10.mm"
include "imp.mm"
include "syl.mm"

theorem bj-rest10b
  let cV: class V
  let cX: class X


  assert |- ( X e. ( V \ { (/) } ) -> ( X |`t (/) ) = { (/) } )

  proof
    cX
    cV
    c0
    csn
    #
    cdif
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    c0
    wne
    #
    wa
    #
    cX
    c0
    crest
    co
    @0
    wceq
    #
    @1
    @2
    cX
    @0
    wcel
    #
    wn
    #
    wa
    @4
    cX
    cV
    @0
    eldif
    @7
    @3
    @2
    @6
    cX
    c0
    wceq
    @3
    cX
    c0
    0ex
    elsn2
    cX
    c0
    neqne
    sylnbi
    anim2i
    sylbi
    @2
    @3
    @5
    cV
    cX
    bj-rest10
    imp
    syl
end
