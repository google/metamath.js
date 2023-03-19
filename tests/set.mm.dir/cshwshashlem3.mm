include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "ccsh.mm"
include "wi.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cr.mm"
include "wb.mm"
include "elfzoelz.mm"
include "zred.mm"
include "lttri2.mm"
include "syl2anr.mm"
include "cshwshashlem2.mm"
include "com12.mm"
include "3expia.mm"
include "imp.mm"
include "necomd.mm"
include "expcom.mm"
include "ancoms.mm"
include "jaod.mm"
include "sylbid.mm"
include "3impia.mm"

theorem cshwshashlem3
  let wph: wff ph
  let vi: setvar i
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vj: setvar j
  assume cshwshash.0: |- ( ph -> ( W e. Word V /\ ( # ` W ) e. Prime ) )

  disjoint L i
  disjoint V i
  disjoint W i
  disjoint i ph
  disjoint K i
  disjoint L j
  disjoint i j
  disjoint V j
  disjoint W j
  disjoint j ph
  assert |- ( ( ph /\ E. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) =/= ( W ` 0 ) ) -> ( ( L e. ( 0 ..^ ( # ` W ) ) /\ K e. ( 0 ..^ ( # ` W ) ) /\ K =/= L ) -> ( W cyclShift L ) =/= ( W cyclShift K ) ) )

  proof
    cL
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    cK
    @1
    wcel
    #
    cK
    cL
    wne
    #
    w3a
    wph
    vi
    cv
    cW
    cfv
    cc0
    cW
    cfv
    wne
    vi
    @1
    wrex
    wa
    #
    cW
    cL
    ccsh
    co
    #
    cW
    cK
    ccsh
    co
    #
    wne
    #
    @2
    @3
    @4
    @5
    @8
    wi
    #
    @2
    @3
    wa
    #
    @4
    cK
    cL
    clt
    wbr
    #
    cL
    cK
    clt
    wbr
    #
    wo
    #
    @9
    @3
    cK
    cr
    wcel
    cL
    cr
    wcel
    @4
    @13
    wb
    @2
    @3
    cK
    cK
    cc0
    @0
    elfzoelz
    zred
    @2
    cL
    cL
    cc0
    @0
    elfzoelz
    zred
    cK
    cL
    lttri2
    syl2anr
    @10
    @11
    @9
    @12
    @2
    @3
    @11
    @9
    @5
    @2
    @3
    @11
    w3a
    @8
    wph
    vi
    cK
    cL
    cV
    cW
    cshwshash.0
    cshwshashlem2
    com12
    3expia
    @3
    @2
    @12
    @9
    wi
    @3
    @2
    @12
    @9
    @5
    @3
    @2
    @12
    w3a
    #
    @8
    @5
    @14
    wa
    @7
    @6
    @5
    @14
    @7
    @6
    wne
    wph
    vi
    cL
    cK
    cV
    cW
    cshwshash.0
    cshwshashlem2
    imp
    necomd
    expcom
    3expia
    ancoms
    jaod
    sylbid
    3impia
    com12
end
