include "cplig.mm"
include "wcel.mm"
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
include "isplig.mm"
include "ibi.mm"
include "simp3d.mm"

theorem tncp
  let cP: class P
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  assume tncp.1: |- P = U. G

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
  assert |- ( G e. Plig -> E. a e. P E. b e. P E. c e. P A. l e. G -. ( a e. l /\ b e. l /\ c e. l ) )

  proof
    cG
    cplig
    wcel
    #
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
    #
    @1
    @2
    @3
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
    #
    @2
    @3
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
    @0
    @4
    @5
    @6
    w3a
    cplig
    cP
    cG
    va
    vb
    vc
    vl
    tncp.1
    isplig
    ibi
    simp3d
end
