include "cv.mm"
include "wne.mm"
include "wel.mm"
include "wa.mm"
include "wreu.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "wn.mm"
include "cplig.mm"
include "wceq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "reueq1.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "raleqbi1dv.mm"
include "raleq.mm"
include "3anbi123d.mm"
include "df-plig.mm"
include "elab2g.mm"

theorem isplig
  let cA: class A
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
  assert |- ( G e. A -> ( G e. Plig <-> ( A. a e. P A. b e. P ( a =/= b -> E! l e. G ( a e. l /\ b e. l ) ) /\ A. l e. G E. a e. P E. b e. P ( a =/= b /\ a e. l /\ b e. l ) /\ E. a e. P E. b e. P E. c e. P A. l e. G -. ( a e. l /\ b e. l /\ c e. l ) ) ) )

  proof
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
    #
    vl
    vx
    cv
    #
    wreu
    #
    wi
    #
    vb
    @4
    cuni
    #
    wral
    #
    va
    @7
    wral
    #
    @0
    @1
    @2
    w3a
    #
    vb
    @7
    wrex
    #
    va
    @7
    wrex
    #
    vl
    @4
    wral
    #
    @1
    @2
    vc
    vl
    wel
    w3a
    wn
    #
    vl
    @4
    wral
    #
    vc
    @7
    wrex
    #
    vb
    @7
    wrex
    #
    va
    @7
    wrex
    #
    w3a
    @0
    @3
    vl
    cG
    wreu
    #
    wi
    #
    vb
    cP
    wral
    #
    va
    cP
    wral
    #
    @10
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    vl
    cG
    wral
    #
    @14
    vl
    cG
    wral
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    w3a
    vx
    cG
    cplig
    cA
    @4
    cG
    wceq
    #
    @9
    @22
    @13
    @25
    @18
    @29
    @30
    @8
    @21
    va
    @7
    cP
    @30
    @7
    cG
    cuni
    cP
    @4
    cG
    unieq
    isplig.1
    syl6eqr
    #
    @30
    @6
    @20
    vb
    @7
    cP
    @31
    @30
    @5
    @19
    @0
    @3
    vl
    @4
    cG
    reueq1
    imbi2d
    raleqbidv
    raleqbidv
    @12
    @24
    vl
    @4
    cG
    @30
    @11
    @23
    va
    @7
    cP
    @31
    @30
    @10
    vb
    @7
    cP
    @31
    rexeqdv
    rexeqbidv
    raleqbi1dv
    @30
    @17
    @28
    va
    @7
    cP
    @31
    @30
    @16
    @27
    vb
    @7
    cP
    @31
    @30
    @15
    @26
    vc
    @7
    cP
    @31
    @14
    vl
    @4
    cG
    raleq
    rexeqbidv
    rexeqbidv
    rexeqbidv
    3anbi123d
    vx
    va
    vb
    vc
    vl
    df-plig
    elab2g
end
