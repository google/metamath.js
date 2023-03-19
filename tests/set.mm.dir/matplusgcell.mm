include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cof.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "matplusg2.mm"
include "oveqd.mm"
include "adantr.mm"
include "df-ov.mm"
include "a1i.mm"
include "cxp.mm"
include "opelxp.mm"
include "cfn.mm"
include "wfn.mm"
include "cbs.mm"
include "cmap.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapfn.mm"
include "syl.mm"
include "adantl.mm"
include "cvv.mm"
include "matrcl.mm"
include "xpfi.mm"
include "anidms.mm"
include "inidm.mm"
include "eqcomi.mm"
include "ofval.mm"
include "sylan2br.mm"
include "3eqtrd.mm"

theorem matplusgcell
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matplusgcell.a: |- A = ( N Mat R )
  assume matplusgcell.b: |- B = ( Base ` A )
  assume matplusgcell.p: |- .+b = ( +g ` A )
  assume matplusgcell.q: |- .+ = ( +g ` R )


  assert |- ( ( ( X e. B /\ Y e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I ( X .+b Y ) J ) = ( ( I X J ) .+ ( I Y J ) ) )

  proof
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
    wa
    #
    cI
    cJ
    cX
    cY
    c.pb
    co
    #
    co
    #
    cI
    cJ
    cX
    cY
    c.pl
    cof
    co
    #
    co
    #
    cI
    cJ
    cop
    #
    @7
    cfv
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
    c.pl
    co
    #
    @2
    @6
    @8
    wceq
    @3
    @2
    @5
    @7
    cI
    cJ
    cA
    cB
    c.pl
    c.pb
    cR
    cN
    cX
    cY
    matplusgcell.a
    matplusgcell.b
    matplusgcell.p
    matplusgcell.q
    matplusg2
    oveqd
    adantr
    @8
    @10
    wceq
    @4
    cI
    cJ
    @7
    df-ov
    a1i
    @3
    @2
    @9
    cN
    cN
    cxp
    #
    wcel
    #
    @10
    @13
    wceq
    cI
    cJ
    cN
    cN
    opelxp
    @2
    @14
    @14
    @11
    @12
    c.pl
    @14
    cX
    cY
    cfn
    cfn
    @9
    @0
    cX
    @14
    wfn
    #
    @1
    @0
    cX
    cR
    cbs
    cfv
    #
    @14
    cmap
    co
    #
    wcel
    @16
    cA
    cB
    cR
    @17
    cX
    cN
    matplusgcell.a
    @17
    eqid
    #
    matplusgcell.b
    matbas2i
    cX
    @17
    @14
    elmapfn
    syl
    adantr
    @1
    cY
    @14
    wfn
    #
    @0
    @1
    cY
    @18
    wcel
    @20
    cA
    cB
    cR
    @17
    cY
    cN
    matplusgcell.a
    @19
    matplusgcell.b
    matbas2i
    cY
    @17
    @14
    elmapfn
    syl
    adantl
    @0
    @14
    cfn
    wcel
    #
    @1
    @0
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    @21
    cA
    cB
    cR
    cN
    cX
    matplusgcell.a
    matplusgcell.b
    matrcl
    @22
    @21
    @23
    @22
    @21
    cN
    cN
    xpfi
    anidms
    adantr
    syl
    adantr
    #
    @24
    @14
    inidm
    @9
    cX
    cfv
    #
    @11
    wceq
    @2
    @15
    wa
    #
    @11
    @25
    cI
    cJ
    cX
    df-ov
    eqcomi
    a1i
    @9
    cY
    cfv
    #
    @12
    wceq
    @26
    @12
    @27
    cI
    cJ
    cY
    df-ov
    eqcomi
    a1i
    ofval
    sylan2br
    3eqtrd
end
