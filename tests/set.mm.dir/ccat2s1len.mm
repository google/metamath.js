include "wcel.mm"
include "cs1.mm"
include "cword.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "s1cl.mm"
include "wa.mm"
include "caddc.mm"
include "ccatlen.mm"
include "c1.mm"
include "s1len.mm"
include "oveq12i.mm"
include "1p1e2.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "syl2an.mm"

theorem ccat2s1len
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. V ) -> ( # ` ( <" X "> ++ <" Y "> ) ) = 2 )

  proof
    cX
    cV
    wcel
    cX
    cs1
    #
    cV
    cword
    #
    wcel
    #
    cY
    cs1
    #
    @1
    wcel
    #
    @0
    @3
    cconcat
    co
    chash
    cfv
    #
    c2
    wceq
    cY
    cV
    wcel
    cX
    cV
    s1cl
    cY
    cV
    s1cl
    @2
    @4
    wa
    @5
    @0
    chash
    cfv
    #
    @3
    chash
    cfv
    #
    caddc
    co
    #
    c2
    cV
    @0
    @3
    ccatlen
    @8
    c1
    c1
    caddc
    co
    c2
    @6
    c1
    @7
    c1
    caddc
    cX
    s1len
    cY
    s1len
    oveq12i
    1p1e2
    eqtri
    syl6eq
    syl2an
end
