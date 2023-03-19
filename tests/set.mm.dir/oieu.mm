include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "word.mm"
include "cep.mm"
include "wiso.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "simprr.mm"
include "ordtype.mm"
include "adantr.mm"
include "isocnv.mm"
include "syl.mm"
include "isotr.mm"
include "syl2anc.mm"
include "simprl.mm"
include "oicl.mm"
include "a1i.mm"
include "ordiso2.mm"
include "syl3anc.mm"
include "ordwe.mm"
include "ad2antrl.mm"
include "epse.mm"
include "wb.mm"
include "isoeq4.mm"
include "mpbird.mm"
include "weisoeq.mm"
include "syl22anc.mm"
include "jca.mm"
include "ex.mm"
include "jctil.mm"
include "ordeq.mm"
include "isoeq1.mm"
include "sylan9bb.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem oieu
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vh: setvar h
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cM: class M
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  assume oicl.1: |- F = OrdIso ( R , A )


  assert |- ( ( R We A /\ R Se A ) -> ( ( Ord B /\ G Isom _E , R ( B , A ) ) <-> ( B = dom F /\ G = F ) ) )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    cB
    word
    #
    cB
    cA
    cep
    cR
    cG
    wiso
    #
    wa
    #
    cB
    cF
    cdm
    #
    wceq
    #
    cG
    cF
    wceq
    #
    wa
    #
    @0
    @3
    @7
    @0
    @3
    wa
    #
    @5
    @6
    @8
    cB
    @4
    cep
    cep
    cF
    ccnv
    #
    cG
    ccom
    #
    wiso
    #
    @1
    @4
    word
    #
    @5
    @8
    @2
    cA
    @4
    cR
    cep
    @9
    wiso
    #
    @11
    @0
    @1
    @2
    simprr
    #
    @8
    @4
    cA
    cep
    cR
    cF
    wiso
    #
    @13
    @0
    @15
    @3
    cA
    cR
    cF
    oicl.1
    ordtype
    #
    adantr
    #
    @4
    cA
    cep
    cR
    cF
    isocnv
    syl
    cB
    cA
    @4
    cep
    cR
    cep
    @9
    cG
    isotr
    syl2anc
    @0
    @1
    @2
    simprl
    @12
    @8
    cA
    cR
    cF
    oicl.1
    oicl
    #
    a1i
    cB
    @4
    @10
    ordiso2
    syl3anc
    #
    @8
    cB
    cep
    wwe
    #
    cB
    cep
    wse
    #
    @2
    cB
    cA
    cep
    cR
    cF
    wiso
    #
    @6
    @1
    @20
    @0
    @2
    cB
    ordwe
    ad2antrl
    @21
    @8
    cB
    epse
    a1i
    @14
    @8
    @22
    @15
    @17
    @8
    @5
    @22
    @15
    wb
    @19
    cB
    cA
    @4
    cep
    cR
    cF
    isoeq4
    syl
    mpbird
    cB
    cA
    cep
    cR
    cG
    cF
    weisoeq
    syl22anc
    jca
    ex
    @0
    @3
    @7
    @12
    @15
    wa
    @0
    @15
    @12
    @16
    @18
    jctil
    @7
    @1
    @12
    @2
    @15
    @5
    @1
    @12
    wb
    @6
    cB
    @4
    ordeq
    adantr
    @5
    @2
    @4
    cA
    cep
    cR
    cG
    wiso
    @6
    @15
    cB
    cA
    @4
    cep
    cR
    cG
    isoeq4
    @4
    cA
    cep
    cR
    cF
    cG
    isoeq1
    sylan9bb
    anbi12d
    syl5ibrcom
    impbid
end
