include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "cvv.mm"
include "cmpt.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simp2.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wa.mm"
include "cur.mm"
include "ifcld.mm"
include "mptsuppd.mm"
include "csn.mm"
include "wss.mm"
include "snfi.mm"
include "wi.mm"
include "wral.mm"
include "2a1.mm"
include "wn.mm"
include "iffalse.mm"
include "adantr.mm"
include "neeq1d.mm"
include "eqid.mm"
include "eqneqall.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "ex.mm"
include "pm2.61i.mm"
include "ralrimiva.mm"
include "rabsssn.mm"
include "sylibr.mm"
include "ssfi.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem suppmptcfin
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vv: setvar v
  let vk: setvar k
  assume suppmptcfin.b: |- B = ( Base ` M )
  assume suppmptcfin.r: |- R = ( Scalar ` M )
  assume suppmptcfin.0: |- .0. = ( 0g ` R )
  assume suppmptcfin.1: |- .1. = ( 1r ` R )
  assume suppmptcfin.f: |- F = ( x e. V |-> if ( x = X , .1. , .0. ) )

  disjoint B x
  disjoint F x
  disjoint M x
  disjoint V x
  disjoint X x
  disjoint .1. x
  disjoint .0. x
  disjoint B v
  disjoint v x
  disjoint F v
  disjoint M v
  disjoint V v
  disjoint X v
  disjoint .1. v
  disjoint .0. v
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P B /\ X e. V ) -> ( F supp .0. ) e. Fin )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cF
    c.0
    csupp
    co
    vv
    cv
    #
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    c.0
    wne
    #
    vv
    cV
    crab
    #
    cfn
    @4
    vv
    cV
    @7
    cvv
    cF
    @1
    cvv
    c.0
    cF
    vx
    cV
    vx
    cv
    #
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    vv
    cV
    @7
    cmpt
    suppmptcfin.f
    vx
    vv
    cV
    @12
    @7
    vx
    vv
    weq
    @11
    @6
    c.1
    c.0
    @10
    @5
    cX
    eqeq1
    ifbid
    cbvmptv
    eqtri
    @0
    @2
    @3
    simp2
    c.0
    cvv
    wcel
    #
    @4
    c.0
    cR
    c0g
    cfv
    cvv
    suppmptcfin.0
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    @4
    @5
    cV
    wcel
    wa
    #
    @6
    c.1
    c.0
    cvv
    c.1
    cvv
    wcel
    @15
    c.1
    cR
    cur
    cfv
    cvv
    suppmptcfin.1
    cR
    cur
    fvex
    eqeltri
    a1i
    @13
    @15
    @14
    a1i
    ifcld
    mptsuppd
    @4
    cX
    csn
    #
    cfn
    wcel
    @9
    @16
    wss
    #
    @9
    cfn
    wcel
    cX
    snfi
    @4
    @8
    @6
    wi
    #
    vv
    cV
    wral
    @17
    @4
    @18
    vv
    cV
    @6
    @15
    @18
    wi
    @6
    @15
    @8
    2a1
    @6
    wn
    #
    @15
    @18
    @19
    @15
    wa
    #
    @8
    c.0
    c.0
    wne
    #
    @6
    @20
    @7
    c.0
    c.0
    @19
    @7
    c.0
    wceq
    @15
    @6
    c.1
    c.0
    iffalse
    adantr
    neeq1d
    c.0
    c.0
    wceq
    @21
    @6
    wi
    c.0
    eqid
    @6
    c.0
    c.0
    eqneqall
    ax-mp
    syl6bi
    ex
    pm2.61i
    ralrimiva
    @8
    vv
    cV
    cX
    rabsssn
    sylibr
    @16
    @9
    ssfi
    sylancr
    eqeltrd
end
