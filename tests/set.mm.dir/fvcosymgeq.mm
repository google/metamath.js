include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "ccom.mm"
include "wfn.mm"
include "cin.mm"
include "crn.mm"
include "wf.mm"
include "symgbasf.mm"
include "ffn.mm"
include "syl.mm"
include "anim12i.mm"
include "adantr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "simpr2.mm"
include "wi.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "wf1.mm"
include "dff1o5.mm"
include "eqcom.mm"
include "sylbi.mm"
include "ineqan12d.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "biimpcd.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "3jca.mm"
include "fvcofneq.mm"
include "sylc.mm"
include "ex.mm"

theorem fvcosymgeq
  let cB: class B
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let cW: class W
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )
  assume gsmsymgreq.z: |- Z = ( SymGrp ` M )
  assume gsmsymgreq.p: |- P = ( Base ` Z )
  assume gsmsymgreq.i: |- I = ( N i^i M )

  disjoint F n
  disjoint G n
  disjoint H n
  disjoint I n
  disjoint K n
  disjoint X n
  disjoint B i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint W i
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint W w
  assert |- ( ( G e. B /\ K e. P ) -> ( ( X e. I /\ ( G ` X ) = ( K ` X ) /\ A. n e. I ( F ` n ) = ( H ` n ) ) -> ( ( F o. G ) ` X ) = ( ( H o. K ) ` X ) ) )

  proof
    cG
    cB
    wcel
    #
    cK
    cP
    wcel
    #
    wa
    #
    cX
    cI
    wcel
    #
    cX
    cG
    cfv
    cX
    cK
    cfv
    wceq
    #
    vn
    cv
    #
    cF
    cfv
    @5
    cH
    cfv
    wceq
    #
    vn
    cI
    wral
    #
    w3a
    #
    cX
    cF
    cG
    ccom
    cfv
    cX
    cH
    cK
    ccom
    cfv
    wceq
    #
    @2
    @8
    wa
    #
    cG
    cN
    wfn
    #
    cK
    cM
    wfn
    #
    wa
    #
    cX
    cN
    cM
    cin
    #
    wcel
    #
    @4
    @6
    vn
    cG
    crn
    #
    cK
    crn
    #
    cin
    #
    wral
    #
    w3a
    @9
    @2
    @13
    @8
    @0
    @11
    @1
    @12
    @0
    cN
    cN
    cG
    wf
    @11
    cN
    cB
    cG
    cS
    gsmsymgrfix.s
    gsmsymgrfix.b
    symgbasf
    cN
    cN
    cG
    ffn
    syl
    @1
    cM
    cM
    cK
    wf
    @12
    cM
    cP
    cK
    cZ
    gsmsymgreq.z
    gsmsymgreq.p
    symgbasf
    cM
    cM
    cK
    ffn
    syl
    anim12i
    adantr
    @10
    @15
    @4
    @19
    @8
    @15
    @2
    @3
    @4
    @15
    @7
    @3
    @15
    cI
    @14
    cX
    gsmsymgreq.i
    eleq2i
    biimpi
    3ad2ant1
    adantl
    @2
    @3
    @4
    @7
    simpr2
    @8
    @2
    @19
    @7
    @3
    @2
    @19
    wi
    @4
    @2
    @7
    @19
    @2
    @6
    vn
    cI
    @18
    @2
    cI
    @14
    @18
    gsmsymgreq.i
    @0
    @1
    cN
    @16
    cM
    @17
    @0
    cN
    cN
    cG
    wf1o
    #
    cN
    @16
    wceq
    #
    cN
    cB
    cG
    cS
    gsmsymgrfix.s
    gsmsymgrfix.b
    symgbasf1o
    @20
    cN
    cN
    cG
    wf1
    #
    @16
    cN
    wceq
    #
    wa
    @21
    cN
    cN
    cG
    dff1o5
    @23
    @21
    @22
    @23
    @21
    @16
    cN
    eqcom
    biimpi
    adantl
    sylbi
    syl
    @1
    cM
    cM
    cK
    wf1o
    #
    cM
    @17
    wceq
    #
    cM
    cP
    cK
    cZ
    gsmsymgreq.z
    gsmsymgreq.p
    symgbasf1o
    @24
    cM
    cM
    cK
    wf1
    #
    @17
    cM
    wceq
    #
    wa
    @25
    cM
    cM
    cK
    dff1o5
    @27
    @25
    @26
    @27
    @25
    @17
    cM
    eqcom
    biimpi
    adantl
    sylbi
    syl
    ineqan12d
    syl5eq
    raleqdv
    biimpcd
    3ad2ant3
    impcom
    3jca
    vn
    cN
    cM
    cF
    cG
    cH
    cK
    cX
    fvcofneq
    sylc
    ex
end
