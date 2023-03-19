include "cplig.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wel.mm"
include "wa.mm"
include "wreu.mm"
include "wral.mm"
include "wn.mm"
include "isplig.mm"
include "wceq.mm"
include "eleq2.mm"
include "3anbi23d.mm"
include "2rexbidv.mm"
include "rspccv.mm"
include "3ad2ant2.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "imp.mm"

theorem l2p
  let cP: class P
  let cG: class G
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  assume l2p.1: |- P = U. G

  disjoint a b
  disjoint G a
  disjoint G b
  disjoint L a
  disjoint L b
  disjoint P a
  disjoint P b
  disjoint a c
  disjoint a l
  disjoint b c
  disjoint b l
  disjoint c l
  disjoint G c
  disjoint G l
  disjoint L l
  disjoint P c
  disjoint P l
  assert |- ( ( G e. Plig /\ L e. G ) -> E. a e. P E. b e. P ( a =/= b /\ a e. L /\ b e. L ) )

  proof
    cG
    cplig
    wcel
    #
    cL
    cG
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    @2
    cL
    wcel
    #
    @3
    cL
    wcel
    #
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    @0
    @1
    @8
    wi
    #
    @0
    @0
    @4
    va
    vl
    wel
    #
    vb
    vl
    wel
    #
    wa
    vl
    cG
    wreu
    wi
    vb
    cP
    wral
    va
    cP
    wral
    #
    @4
    @10
    @11
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    vl
    cG
    wral
    #
    @10
    @11
    vc
    vl
    wel
    w3a
    wn
    vl
    cG
    wral
    vc
    cP
    wrex
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    w3a
    @9
    cplig
    cP
    cG
    va
    vb
    vc
    vl
    l2p.1
    isplig
    @15
    @12
    @9
    @16
    @14
    @8
    vl
    cL
    cG
    vl
    cv
    #
    cL
    wceq
    #
    @13
    @7
    va
    vb
    cP
    cP
    @18
    @10
    @5
    @11
    @6
    @4
    @17
    cL
    @2
    eleq2
    @17
    cL
    @3
    eleq2
    3anbi23d
    2rexbidv
    rspccv
    3ad2ant2
    syl6bi
    pm2.43i
    imp
end
