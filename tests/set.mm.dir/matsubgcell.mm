include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cof.mm"
include "cxp.mm"
include "cfrlm.mm"
include "csg.mm"
include "cfv.mm"
include "cfn.mm"
include "wceq.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "eqid.mm"
include "matsubg.mm"
include "syl2anc.mm"
include "syl6reqr.mm"
include "oveqd.mm"
include "cbs.mm"
include "xpfi.mm"
include "anidms.mm"
include "syl.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "matbas.mm"
include "eleqtrrd.mm"
include "adantl.mm"
include "frlmsubgval.mm"
include "eqtrd.mm"
include "cop.mm"
include "df-ov.mm"
include "opelxpi.mm"
include "anim2i.mm"
include "3adant1.mm"
include "wfn.mm"
include "cmap.mm"
include "matbas2i.mm"
include "elmapfn.mm"
include "inidm.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ofval.mm"
include "syl5eq.mm"

theorem matsubgcell
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matplusgcell.a: |- A = ( N Mat R )
  assume matplusgcell.b: |- B = ( Base ` A )
  assume matsubgcell.s: |- S = ( -g ` A )
  assume matsubgcell.m: |- .- = ( -g ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I ( X S Y ) J ) = ( ( I X J ) .- ( I Y J ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    cJ
    cN
    wcel
    wa
    #
    w3a
    #
    cI
    cJ
    cX
    cY
    cS
    co
    #
    co
    cI
    cJ
    cX
    cY
    c.mi
    cof
    co
    #
    co
    #
    cI
    cJ
    cX
    co
    #
    cI
    cJ
    cY
    co
    #
    c.mi
    co
    #
    @5
    @6
    @7
    cI
    cJ
    @5
    @6
    cX
    cY
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    csg
    cfv
    #
    co
    @7
    @5
    cS
    @14
    cX
    cY
    @5
    @14
    cA
    csg
    cfv
    #
    cS
    @5
    cN
    cfn
    wcel
    #
    @0
    @14
    @15
    wceq
    @3
    @0
    @16
    @4
    @1
    @16
    @2
    @1
    @16
    cR
    cvv
    wcel
    #
    cA
    cB
    cR
    cN
    cX
    matplusgcell.a
    matplusgcell.b
    matrcl
    #
    simpld
    adantr
    3ad2ant2
    @0
    @3
    @4
    simp1
    #
    cA
    cR
    @13
    cN
    crg
    matplusgcell.a
    @13
    eqid
    #
    matsubg
    syl2anc
    matsubgcell.s
    syl6reqr
    oveqd
    @5
    @13
    cbs
    cfv
    #
    cR
    cX
    cY
    @12
    @14
    c.mi
    cfn
    @13
    @20
    @21
    eqid
    @19
    @3
    @0
    @12
    cfn
    wcel
    #
    @4
    @1
    @22
    @2
    @1
    @16
    @17
    wa
    #
    @22
    @18
    @16
    @22
    @17
    @16
    @22
    cN
    cN
    xpfi
    anidms
    adantr
    syl
    adantr
    #
    3ad2ant2
    @3
    @0
    cX
    @21
    wcel
    #
    @4
    @1
    @25
    @2
    @1
    cX
    cA
    cbs
    cfv
    #
    @21
    @1
    cX
    @26
    wcel
    cB
    @26
    cX
    matplusgcell.b
    eleq2i
    biimpi
    @1
    @23
    @21
    @26
    wceq
    #
    @18
    cA
    cR
    @13
    cN
    cvv
    matplusgcell.a
    @20
    matbas
    #
    syl
    eleqtrrd
    adantr
    3ad2ant2
    @3
    @0
    cY
    @21
    wcel
    #
    @4
    @2
    @29
    @1
    @2
    cY
    @26
    @21
    @2
    cY
    @26
    wcel
    cB
    @26
    cY
    matplusgcell.b
    eleq2i
    biimpi
    @2
    @23
    @27
    cA
    cB
    cR
    cN
    cY
    matplusgcell.a
    matplusgcell.b
    matrcl
    @28
    syl
    eleqtrrd
    adantl
    3ad2ant2
    matsubgcell.m
    @14
    eqid
    frlmsubgval
    eqtrd
    oveqd
    @5
    @8
    cI
    cJ
    cop
    #
    @7
    cfv
    #
    @11
    cI
    cJ
    @7
    df-ov
    @5
    @3
    @30
    @12
    wcel
    #
    wa
    #
    @31
    @11
    wceq
    @3
    @4
    @33
    @0
    @4
    @32
    @3
    cI
    cJ
    cN
    cN
    opelxpi
    anim2i
    3adant1
    @3
    @12
    @12
    @9
    @10
    c.mi
    @12
    cX
    cY
    cfn
    cfn
    @30
    @1
    cX
    @12
    wfn
    #
    @2
    @1
    cX
    cR
    cbs
    cfv
    #
    @12
    cmap
    co
    #
    wcel
    @34
    cA
    cB
    cR
    @35
    cX
    cN
    matplusgcell.a
    @35
    eqid
    #
    matplusgcell.b
    matbas2i
    cX
    @35
    @12
    elmapfn
    syl
    adantr
    @2
    cY
    @12
    wfn
    #
    @1
    @2
    cY
    @36
    wcel
    @38
    cA
    cB
    cR
    @35
    cY
    cN
    matplusgcell.a
    @37
    matplusgcell.b
    matbas2i
    cY
    @35
    @12
    elmapfn
    syl
    adantl
    @24
    @24
    @12
    inidm
    @30
    cX
    cfv
    #
    @9
    wceq
    @33
    @9
    @39
    cI
    cJ
    cX
    df-ov
    eqcomi
    a1i
    @30
    cY
    cfv
    #
    @10
    wceq
    @33
    @10
    @40
    cI
    cJ
    cY
    df-ov
    eqcomi
    a1i
    ofval
    syl
    syl5eq
    eqtrd
end
