include "cuhgr.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "id.mm"
include "wceq.mm"
include "wb.mm"
include "sseq2.mm"
include "adantl.mm"
include "ssid.mm"
include "a1i.mm"
include "rspcedvd.mm"
include "3anim3i.mm"
include "1pthon2v.mm"
include "syl.mm"

theorem 1pthon2ve
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let ve: setvar e
  let vi: setvar i
  assume 1pthon2v.v: |- V = ( Vtx ` G )
  assume 1pthon2v.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint G f
  disjoint G p
  disjoint A e
  disjoint A i
  disjoint e f
  disjoint e i
  disjoint e p
  disjoint f i
  disjoint i p
  disjoint B e
  disjoint B i
  disjoint G e
  disjoint G i
  disjoint V e
  disjoint V i
  disjoint E e
  assert |- ( ( G e. UHGraph /\ ( A e. V /\ B e. V ) /\ { A , B } e. E ) -> E. f E. p f ( A ( PathsOn ` G ) B ) p )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    w3a
    @0
    @1
    @2
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    w3a
    vf
    cv
    vp
    cv
    cA
    cB
    cG
    cpthson
    cfv
    co
    wbr
    vp
    wex
    vf
    wex
    @3
    @6
    @0
    @1
    @3
    @5
    @2
    @2
    wss
    #
    ve
    @2
    cE
    @3
    id
    @4
    @2
    wceq
    @5
    @7
    wb
    @3
    @4
    @2
    @2
    sseq2
    adantl
    @7
    @3
    @2
    ssid
    a1i
    rspcedvd
    3anim3i
    cA
    cB
    ve
    vf
    cE
    cG
    cV
    vp
    1pthon2v.v
    1pthon2v.e
    1pthon2v
    syl
end
