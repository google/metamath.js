include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "cuni.mm"
include "cres.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "funres11.mm"
include "funcnvcnv.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "anim12i.mm"
include "cima.mm"
include "df-ima.mm"
include "df-rn.mm"
include "eqtr2i.mm"
include "eqtri.mm"
include "sbthlem4.mm"
include "syl5eqr.mm"
include "ineq12.mm"
include "sylancr.mm"
include "disjdif.mm"
include "syl6eq.mm"
include "adantlll.mm"
include "adantl.mm"
include "funun.mm"
include "syl2anc.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem sbthlem8
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }
  assume sbthlem.3: |- H = ( ( f |` U. D ) u. ( `' g |` ( A \ U. D ) ) )

  disjoint H x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ( Fun `' f /\ ( ( ( Fun g /\ dom g = B ) /\ ran g C_ A ) /\ Fun `' g ) ) -> Fun `' H )

  proof
    vf
    cv
    #
    ccnv
    wfun
    #
    vg
    cv
    #
    wfun
    #
    @2
    cdm
    cB
    wceq
    #
    wa
    @2
    crn
    cA
    wss
    #
    wa
    @2
    ccnv
    #
    wfun
    #
    wa
    #
    wa
    #
    @0
    cD
    cuni
    #
    cres
    #
    ccnv
    #
    @6
    cA
    @10
    cdif
    #
    cres
    #
    ccnv
    #
    cun
    #
    wfun
    #
    cH
    ccnv
    #
    wfun
    @9
    @12
    wfun
    #
    @15
    wfun
    #
    wa
    @12
    cdm
    #
    @15
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @17
    @1
    @19
    @8
    @20
    @10
    @0
    funres11
    @3
    @20
    @4
    @5
    @7
    @3
    @6
    ccnv
    wfun
    @20
    @2
    funcnvcnv
    @13
    @6
    funres11
    syl
    ad3antrrr
    anim12i
    @8
    @24
    @1
    @4
    @5
    @7
    @24
    @3
    @4
    @5
    wa
    @7
    wa
    #
    @23
    @0
    @10
    cima
    #
    cB
    @26
    cdif
    #
    cin
    #
    c0
    @25
    @21
    @26
    wceq
    @22
    @27
    wceq
    @23
    @28
    wceq
    @26
    @11
    crn
    @21
    @0
    @10
    df-ima
    @11
    df-rn
    eqtr2i
    @25
    @22
    @6
    @13
    cima
    #
    @27
    @29
    @14
    crn
    @22
    @6
    @13
    df-ima
    @14
    df-rn
    eqtri
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem4
    syl5eqr
    @21
    @26
    @22
    @27
    ineq12
    sylancr
    @26
    cB
    disjdif
    syl6eq
    adantlll
    adantl
    @12
    @15
    funun
    syl2anc
    @18
    @16
    @18
    @11
    @14
    cun
    #
    ccnv
    @16
    cH
    @30
    sbthlem.3
    cnveqi
    @11
    @14
    cnvun
    eqtri
    funeqi
    sylibr
end
