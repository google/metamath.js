include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "cword.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "c1.mm"
include "wo.mm"
include "wi.mm"
include "creps.mm"
include "wb.mm"
include "repswsymballbi.mm"
include "adantr.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "prmnn.mm"
include "nnge1d.mm"
include "wrdsymb1.mm"
include "sylan2.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "cshwrepswhash1.mm"
include "syl3anc.mm"
include "ex.mm"
include "sylbird.mm"
include "olc.mm"
include "syl6com.mm"
include "wn.mm"
include "wne.mm"
include "wrex.mm"
include "rexnal.mm"
include "df-ne.mm"
include "bicomi.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "cshwshashnsame.mm"
include "orc.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem cshwshash
  let vw: setvar w
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cW: class W
  let cA: class A
  let vi: setvar i
  let vu: setvar u
  let vr: setvar r
  let cN: class N
  assume cshwrepswhash1.m: |- M = { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w }

  disjoint V n
  disjoint V w
  disjoint n w
  disjoint W n
  disjoint W w
  disjoint A i
  disjoint A n
  disjoint A u
  disjoint A w
  disjoint i n
  disjoint i u
  disjoint i w
  disjoint n u
  disjoint u w
  disjoint M r
  disjoint N i
  disjoint N n
  disjoint N u
  disjoint N w
  disjoint V r
  disjoint V u
  disjoint n r
  disjoint r u
  disjoint r w
  disjoint W i
  disjoint W r
  disjoint W u
  disjoint i r
  disjoint V i
  assert |- ( ( W e. Word V /\ ( # ` W ) e. Prime ) -> ( ( # ` M ) = ( # ` W ) \/ ( # ` M ) = 1 ) )

  proof
    vi
    cv
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    wceq
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cW
    cV
    cword
    wcel
    #
    @3
    cprime
    wcel
    #
    wa
    #
    cM
    chash
    cfv
    #
    @3
    wceq
    #
    @9
    c1
    wceq
    #
    wo
    #
    wi
    #
    @8
    @5
    @11
    @12
    @8
    @5
    cW
    @1
    @3
    creps
    co
    wceq
    #
    @11
    @6
    @14
    @5
    wb
    @7
    vi
    cV
    cW
    repswsymballbi
    adantr
    @8
    @14
    @11
    @8
    @14
    wa
    @1
    cV
    wcel
    #
    @3
    cn
    wcel
    #
    @14
    @11
    @8
    @15
    @14
    @7
    @6
    c1
    @3
    cle
    wbr
    @15
    @7
    @3
    @3
    prmnn
    #
    nnge1d
    cV
    cW
    wrdsymb1
    sylan2
    adantr
    @7
    @16
    @6
    @14
    @17
    ad2antlr
    @8
    @14
    simpr
    vw
    @1
    vn
    cM
    @3
    cV
    cW
    cshwrepswhash1.m
    cshwrepswhash1
    syl3anc
    ex
    sylbird
    @11
    @10
    olc
    syl6com
    @5
    wn
    #
    @0
    @1
    wne
    #
    vi
    @4
    wrex
    #
    @13
    @18
    @2
    wn
    #
    vi
    @4
    wrex
    @20
    @2
    vi
    @4
    rexnal
    @21
    @19
    vi
    @4
    @19
    @21
    @0
    @1
    df-ne
    bicomi
    rexbii
    bitr3i
    @8
    @20
    @10
    @12
    vw
    vi
    vn
    cM
    cV
    cW
    cshwrepswhash1.m
    cshwshashnsame
    @10
    @11
    orc
    syl6com
    sylbi
    pm2.61i
end
