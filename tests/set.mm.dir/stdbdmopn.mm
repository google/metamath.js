include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cmopn.mm"
include "cif.mm"
include "cr.mm"
include "rpxr.mm"
include "ad2antll.mm"
include "simpl2.mm"
include "ifcld.mm"
include "rpre.mm"
include "rpgt0.mm"
include "simpl3.mm"
include "breq2.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "wi.mm"
include "0xr.mm"
include "xrltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "xrmin1.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "elrpd.mm"
include "simprl.mm"
include "xrmin2.mm"
include "3jca.mm"
include "stdbdbl.mm"
include "syldan.mm"
include "eqcomd.mm"
include "breq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimivva.mm"
include "simp1.mm"
include "stdbdxmet.mm"
include "eqid.mm"
include "metequiv2.mm"

theorem stdbdmopn
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cJ: class J
  let cX: class X
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cS: class S
  let cB: class B
  let cP: class P
  assume stdbdmet.1: |- D = ( x e. X , y e. X |-> if ( ( x C y ) <_ R , ( x C y ) , R ) )
  assume stdbdmopn.2: |- J = ( MetOpen ` C )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J z
  disjoint S z
  disjoint B x
  disjoint B y
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( C e. ( *Met ` X ) /\ R e. RR* /\ 0 < R ) -> J = ( MetOpen ` D ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    w3a
    #
    vs
    cv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vz
    cv
    #
    @5
    cC
    cbl
    cfv
    #
    co
    #
    @8
    @5
    cD
    cbl
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    vz
    cX
    wral
    #
    cJ
    cD
    cmopn
    cfv
    #
    wceq
    #
    @4
    @15
    vz
    vr
    cX
    crp
    @4
    @8
    cX
    wcel
    #
    @6
    crp
    wcel
    #
    wa
    #
    wa
    #
    @6
    cR
    cle
    wbr
    #
    @6
    cR
    cif
    #
    crp
    wcel
    @24
    @6
    cle
    wbr
    #
    @8
    @24
    @9
    co
    #
    @8
    @24
    @11
    co
    #
    wceq
    #
    @15
    @22
    @24
    @22
    @24
    cxr
    wcel
    #
    @6
    cr
    wcel
    #
    cc0
    @24
    cle
    wbr
    #
    @25
    @24
    cr
    wcel
    @22
    @23
    @6
    cR
    cxr
    @20
    @6
    cxr
    wcel
    #
    @4
    @19
    @6
    rpxr
    ad2antll
    #
    @1
    @2
    @3
    @21
    simpl2
    #
    ifcld
    #
    @20
    @30
    @4
    @19
    @6
    rpre
    ad2antll
    @22
    cc0
    @24
    clt
    wbr
    #
    @31
    @22
    cc0
    @6
    clt
    wbr
    #
    @3
    @36
    @20
    @37
    @4
    @19
    @6
    rpgt0
    ad2antll
    @1
    @2
    @3
    @21
    simpl3
    @23
    @37
    @3
    @36
    @6
    cR
    @6
    @24
    cc0
    clt
    breq2
    cR
    @24
    cc0
    clt
    breq2
    ifboth
    syl2anc
    #
    @22
    cc0
    cxr
    wcel
    @29
    @36
    @31
    wi
    0xr
    @35
    cc0
    @24
    xrltle
    sylancr
    mpd
    @22
    @32
    @2
    @25
    @33
    @34
    @6
    cR
    xrmin1
    syl2anc
    #
    @24
    @6
    xrrege0
    syl22anc
    @38
    elrpd
    @39
    @22
    @27
    @26
    @4
    @21
    @19
    @29
    @24
    cR
    cle
    wbr
    #
    w3a
    @27
    @26
    wceq
    @22
    @19
    @29
    @40
    @4
    @19
    @20
    simprl
    @35
    @22
    @32
    @2
    @40
    @33
    @34
    @6
    cR
    xrmin2
    syl2anc
    3jca
    vx
    vy
    cC
    cD
    @8
    cR
    @24
    cX
    stdbdmet.1
    stdbdbl
    syldan
    eqcomd
    @14
    @25
    @28
    wa
    vs
    @24
    crp
    @5
    @24
    wceq
    #
    @7
    @25
    @13
    @28
    @5
    @24
    @6
    cle
    breq1
    @41
    @10
    @26
    @12
    @27
    @5
    @24
    @8
    @9
    oveq2
    @5
    @24
    @8
    @11
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
    ralrimivva
    @4
    @1
    cD
    @0
    wcel
    @16
    @18
    wi
    @1
    @2
    @3
    simp1
    vx
    vy
    cC
    cD
    cR
    cX
    stdbdmet.1
    stdbdxmet
    vz
    cC
    cD
    cJ
    @17
    cX
    vs
    vr
    stdbdmopn.2
    @17
    eqid
    metequiv2
    syl2anc
    mpd
end
