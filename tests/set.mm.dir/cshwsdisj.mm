include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "ccsh.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "necom.mm"
include "biimpi.mm"
include "adantr.mm"
include "w3a.mm"
include "cshwshashlem3.mm"
include "imp.mm"
include "syl13anc.mm"
include "disjsn2.mm"
include "syl.mm"
include "olcd.mm"
include "ex.mm"
include "pm2.61ine.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "sneqd.mm"
include "disjor.mm"
include "sylibr.mm"

theorem cshwsdisj
  let wph: wff ph
  let vi: setvar i
  let vn: setvar n
  let cV: class V
  let cW: class W
  let cL: class L
  let vj: setvar j
  let cK: class K
  assume cshwshash.0: |- ( ph -> ( W e. Word V /\ ( # ` W ) e. Prime ) )

  disjoint V i
  disjoint W i
  disjoint i ph
  disjoint i n
  disjoint n ph
  disjoint W n
  disjoint L i
  disjoint L j
  disjoint i j
  disjoint V j
  disjoint W j
  disjoint j ph
  disjoint K i
  disjoint j n
  assert |- ( ( ph /\ E. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) =/= ( W ` 0 ) ) -> Disj_ n e. ( 0 ..^ ( # ` W ) ) { ( W cyclShift n ) } )

  proof
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
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    wrex
    wa
    #
    vn
    vj
    weq
    #
    cW
    vn
    cv
    #
    ccsh
    co
    #
    csn
    #
    cW
    vj
    cv
    #
    ccsh
    co
    #
    csn
    #
    cin
    c0
    wceq
    #
    wo
    #
    vj
    @0
    wral
    vn
    @0
    wral
    vn
    @0
    @5
    wdisj
    @1
    @10
    vn
    vj
    @0
    @0
    @1
    @3
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    wa
    #
    @10
    wi
    @3
    @6
    @2
    @10
    @14
    @2
    @9
    orc
    a1d
    @3
    @6
    wne
    #
    @14
    @10
    @15
    @14
    wa
    #
    @9
    @2
    @16
    @4
    @7
    wne
    #
    @9
    @16
    @1
    @11
    @12
    @6
    @3
    wne
    #
    @17
    @15
    @1
    @13
    simprl
    @15
    @1
    @11
    @12
    simprrl
    @15
    @1
    @11
    @12
    simprrr
    @15
    @18
    @14
    @15
    @18
    @3
    @6
    necom
    biimpi
    adantr
    @1
    @11
    @12
    @18
    w3a
    @17
    wph
    vi
    @6
    @3
    cV
    cW
    cshwshash.0
    cshwshashlem3
    imp
    syl13anc
    @4
    @7
    disjsn2
    syl
    olcd
    ex
    pm2.61ine
    ralrimivva
    @0
    @5
    @8
    vn
    vj
    @2
    @4
    @7
    @3
    @6
    cW
    ccsh
    oveq2
    sneqd
    disjor
    sylibr
end
