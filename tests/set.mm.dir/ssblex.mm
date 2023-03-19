include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "cbl.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "simprl.mm"
include "rphalfcld.mm"
include "simprr.mm"
include "ifcld.mm"
include "rpred.mm"
include "cr.mm"
include "min1.mm"
include "syl2anc.mm"
include "cc0.mm"
include "rpgt0d.mm"
include "wb.mm"
include "halfpos.mm"
include "syl.mm"
include "mpbid.mm"
include "lelttrd.mm"
include "cxr.mm"
include "simpl.mm"
include "rpxrd.mm"
include "min2.mm"
include "ssbl.mm"
include "syl121anc.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem ssblex
  let vx: setvar x
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C

  disjoint D x
  disjoint R x
  disjoint P x
  disjoint S x
  disjoint X x
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D r
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint P r
  disjoint P y
  disjoint P z
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X ) /\ ( R e. RR+ /\ S e. RR+ ) ) -> E. x e. RR+ ( x < R /\ ( P ( ball ` D ) x ) C_ ( P ( ball ` D ) S ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cP
    cX
    wcel
    wa
    #
    cR
    crp
    wcel
    #
    cS
    crp
    wcel
    #
    wa
    #
    wa
    #
    cR
    c2
    cdiv
    co
    #
    cS
    cle
    wbr
    #
    @5
    cS
    cif
    #
    crp
    wcel
    @7
    cR
    clt
    wbr
    #
    cP
    @7
    cD
    cbl
    cfv
    #
    co
    #
    cP
    cS
    @9
    co
    #
    wss
    #
    vx
    cv
    #
    cR
    clt
    wbr
    #
    cP
    @13
    @9
    co
    #
    @11
    wss
    #
    wa
    #
    vx
    crp
    wrex
    @4
    @6
    @5
    cS
    crp
    @4
    cR
    @0
    @1
    @2
    simprl
    #
    rphalfcld
    #
    @0
    @1
    @2
    simprr
    #
    ifcld
    #
    @4
    @7
    @5
    cR
    @4
    @7
    @21
    rpred
    @4
    @5
    @19
    rpred
    #
    @4
    cR
    @18
    rpred
    #
    @4
    @5
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    @7
    @5
    cle
    wbr
    @22
    @4
    cS
    @20
    rpred
    #
    @5
    cS
    min1
    syl2anc
    @4
    cc0
    cR
    clt
    wbr
    #
    @5
    cR
    clt
    wbr
    #
    @4
    cR
    @18
    rpgt0d
    @4
    cR
    cr
    wcel
    @27
    @28
    wb
    @23
    cR
    halfpos
    syl
    mpbid
    lelttrd
    @4
    @0
    @7
    cxr
    wcel
    cS
    cxr
    wcel
    @7
    cS
    cle
    wbr
    #
    @12
    @0
    @3
    simpl
    @4
    @7
    @21
    rpxrd
    @4
    cS
    @20
    rpxrd
    @4
    @24
    @25
    @29
    @22
    @26
    @5
    cS
    min2
    syl2anc
    cD
    cP
    @7
    cS
    cX
    ssbl
    syl121anc
    @17
    @8
    @12
    wa
    vx
    @7
    crp
    @13
    @7
    wceq
    #
    @14
    @8
    @16
    @12
    @13
    @7
    cR
    clt
    breq1
    @30
    @15
    @10
    @11
    @13
    @7
    cP
    @9
    oveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
end
