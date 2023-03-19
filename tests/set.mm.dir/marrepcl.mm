include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cmarrep.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "marrepval.mm"
include "3adantl1.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "simpl1.mm"
include "simp3.mm"
include "ring0cl.mm"
include "3ad2ant1.mm"
include "ifcld.mm"
include "simp2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "matecl.mm"
include "syl3anc.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem marrepcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume marrepcl.a: |- A = ( N Mat R )
  assume marrepcl.b: |- B = ( Base ` A )


  assert |- ( ( ( R e. Ring /\ M e. B /\ S e. ( Base ` R ) ) /\ ( K e. N /\ L e. N ) ) -> ( K ( M ( N matRRep R ) S ) L ) e. B )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    cK
    cN
    wcel
    cL
    cN
    wcel
    wa
    #
    wa
    #
    cK
    cL
    cM
    cS
    cN
    cR
    cmarrep
    co
    #
    co
    co
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cK
    wceq
    #
    vj
    cv
    #
    cL
    wceq
    #
    cS
    cR
    c0g
    cfv
    #
    cif
    #
    @9
    @11
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cB
    @1
    @3
    @5
    @8
    @17
    wceq
    @0
    cA
    cB
    @7
    cR
    cS
    vi
    vj
    cK
    cL
    cM
    cN
    @13
    marrepcl.a
    marrepcl.b
    @7
    eqid
    @13
    eqid
    #
    marrepval
    3adantl1
    @6
    vi
    vj
    cA
    cB
    @16
    cR
    @2
    cN
    crg
    marrepcl.a
    @2
    eqid
    #
    marrepcl.b
    @4
    cN
    cfn
    wcel
    #
    @5
    @1
    @0
    @20
    @3
    @1
    @20
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marrepcl.a
    marrepcl.b
    matrcl
    simpld
    3ad2ant2
    adantr
    @0
    @1
    @3
    @5
    simpl1
    @6
    @9
    cN
    wcel
    #
    @11
    cN
    wcel
    #
    w3a
    #
    @10
    @14
    @15
    @2
    @6
    @21
    @14
    @2
    wcel
    #
    @22
    @4
    @24
    @5
    @4
    @12
    cS
    @13
    @2
    @0
    @1
    @3
    simp3
    @0
    @1
    @13
    @2
    wcel
    @3
    @2
    cR
    @13
    @19
    @18
    ring0cl
    3ad2ant1
    ifcld
    adantr
    3ad2ant1
    @23
    @21
    @22
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @15
    @2
    wcel
    @6
    @21
    @22
    simp2
    @6
    @21
    @22
    simp3
    @6
    @21
    @26
    @22
    @4
    @26
    @5
    @1
    @0
    @26
    @3
    @1
    @26
    cB
    @25
    cM
    marrepcl.b
    eleq2i
    biimpi
    3ad2ant2
    adantr
    3ad2ant1
    cA
    cR
    @9
    @11
    @2
    cM
    cN
    marrepcl.a
    @19
    matecl
    syl3anc
    ifcld
    matbas2d
    eqeltrd
end
