include "ccusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cedg.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cusgr.mm"
include "wi.mm"
include "cusgrusgr.mm"
include "wa.mm"
include "cfusgr.mm"
include "isfusgr.mm"
include "fusgrfis.mm"
include "sylbir.mm"
include "a1d.mm"
include "ex.mm"
include "syl.mm"
include "3imp.mm"
include "cv.mm"
include "crab.mm"
include "cun.mm"
include "eqid.mm"
include "elnelun.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cin.mm"
include "c0.mm"
include "eleq1i.mm"
include "rabfi.mm"
include "sylbi.mm"
include "adantl.mm"
include "wb.mm"
include "anim1i.mm"
include "sylibr.mm"
include "usgrfilem.mm"
include "stoic3.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "elneldisj.mm"
include "hashun.mm"
include "syl3anc.mm"
include "cusgrsizeindslem.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "mpdan.mm"

theorem cusgrsizeinds
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vn: setvar n
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )
  assume cusgrsizeinds.f: |- F = { e e. E | N e/ e }

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint E f
  disjoint E n
  disjoint e f
  disjoint e n
  disjoint f n
  disjoint G f
  disjoint G n
  disjoint N f
  disjoint N n
  disjoint V f
  disjoint V n
  assert |- ( ( G e. ComplUSGraph /\ V e. Fin /\ N e. V ) -> ( # ` E ) = ( ( ( # ` V ) - 1 ) + ( # ` F ) ) )

  proof
    cG
    ccusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cN
    cV
    wcel
    #
    w3a
    #
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    cE
    chash
    cfv
    #
    cV
    chash
    cfv
    c1
    cmin
    co
    #
    cF
    chash
    cfv
    #
    caddc
    co
    #
    wceq
    @0
    @1
    @2
    @5
    @0
    cG
    cusgr
    wcel
    #
    @1
    @2
    @5
    wi
    #
    wi
    cG
    cusgrusgr
    #
    @10
    @1
    @11
    @10
    @1
    wa
    #
    @5
    @2
    @13
    cG
    cfusgr
    wcel
    #
    @5
    cG
    cV
    cusgrsizeindb0.v
    isfusgr
    #
    cG
    fusgrfis
    sylbir
    a1d
    ex
    syl
    3imp
    @3
    @5
    wa
    #
    @6
    cN
    ve
    cv
    #
    wcel
    #
    ve
    cE
    crab
    #
    cF
    cun
    #
    chash
    cfv
    #
    @19
    chash
    cfv
    #
    @8
    caddc
    co
    #
    @9
    @6
    @21
    wceq
    @16
    cE
    @20
    chash
    @20
    cE
    cE
    cN
    @17
    @19
    cF
    ve
    @19
    eqid
    #
    cusgrsizeinds.f
    elnelun
    eqcomi
    fveq2i
    a1i
    @16
    @19
    cfn
    wcel
    #
    cF
    cfn
    wcel
    #
    @19
    cF
    cin
    c0
    wceq
    #
    @21
    @23
    wceq
    @5
    @25
    @3
    @5
    cE
    cfn
    wcel
    #
    @25
    @4
    cE
    cfn
    cE
    @4
    cusgrsizeindb0.e
    eqcomi
    eleq1i
    #
    @18
    ve
    cE
    rabfi
    sylbi
    adantl
    @3
    @5
    @26
    @5
    @28
    @3
    @26
    @29
    @0
    @1
    @14
    @2
    @28
    @26
    wb
    @0
    @1
    wa
    @13
    @14
    @0
    @10
    @1
    @12
    anim1i
    @15
    sylibr
    ve
    cE
    cF
    cG
    cN
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    cusgrsizeinds.f
    usgrfilem
    stoic3
    syl5bb
    biimpa
    @27
    @16
    cE
    cN
    @17
    @19
    cF
    ve
    @24
    cusgrsizeinds.f
    elneldisj
    a1i
    @19
    cF
    hashun
    syl3anc
    @16
    @22
    @7
    @8
    caddc
    @3
    @22
    @7
    wceq
    @5
    ve
    cE
    cG
    cN
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    cusgrsizeindslem
    adantr
    oveq1d
    3eqtrd
    mpdan
end
