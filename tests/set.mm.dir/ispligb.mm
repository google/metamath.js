include "cplig.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wne.mm"
include "wel.mm"
include "wa.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "wn.mm"
include "elex.mm"
include "isplig.mm"
include "biadan2.mm"

theorem ispligb
  let cP: class P
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  let vx: setvar x
  assume isplig.1: |- P = U. G

  disjoint a b
  disjoint a c
  disjoint a l
  disjoint G a
  disjoint b c
  disjoint b l
  disjoint G b
  disjoint c l
  disjoint G c
  disjoint G l
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint l x
  disjoint G x
  disjoint P x
  assert |- ( G e. Plig <-> ( G e. _V /\ ( A. a e. P A. b e. P ( a =/= b -> E! l e. G ( a e. l /\ b e. l ) ) /\ A. l e. G E. a e. P E. b e. P ( a =/= b /\ a e. l /\ b e. l ) /\ E. a e. P E. b e. P E. c e. P A. l e. G -. ( a e. l /\ b e. l /\ c e. l ) ) ) )

  proof
    cG
    cplig
    wcel
    cG
    cvv
    wcel
    va
    cv
    vb
    cv
    wne
    #
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
    @0
    @1
    @2
    w3a
    vb
    cP
    wrex
    va
    cP
    wrex
    vl
    cG
    wral
    @1
    @2
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
    w3a
    cG
    cplig
    elex
    cvv
    cP
    cG
    va
    vb
    vc
    vl
    isplig.1
    isplig
    biadan2
end
