include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "citg1.mm"
include "cmul.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cof.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "simpl3.mm"
include "wa.mm"
include "1re.mm"
include "0re.mm"
include "keepel.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "ovif2.mm"
include "simp3.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "recnd.mm"
include "mulid1d.mm"
include "mul01d.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "eqid.mm"
include "i1f1.mm"
include "3adant3.mm"
include "i1fmulc.mm"
include "eqeltrrd.mm"
include "wral.mm"
include "simprd.mm"
include "0le0.mm"
include "breq2.mm"
include "ifboth.mm"
include "sylancl.mm"
include "ralrimivw.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "wfn.mm"
include "adantr.mm"
include "ifcl.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "syl.mm"
include "0pledm.mm"
include "ofrfval2.mm"
include "bitrd.mm"
include "mpbird.mm"
include "itg2itg1.mm"
include "syl2anc.mm"
include "itg1mulc.mm"
include "fveq2d.mm"
include "itg11.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem itg2const
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vg: setvar g
  let vz: setvar z
  let vh: setvar h
  let vy: setvar y
  let cF: class F
  let cG: class G

  disjoint A x
  disjoint B x
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint g h
  disjoint g y
  disjoint F g
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint x y
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G g
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR /\ B e. ( 0 [,) +oo ) ) -> ( S.2 ` ( x e. RR |-> if ( x e. A , B , 0 ) ) ) = ( B x. ( vol ` A ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    cB
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    w3a
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @9
    citg1
    cfv
    #
    cB
    @1
    cmul
    co
    #
    @5
    @9
    citg1
    cdm
    #
    wcel
    c0p
    @9
    cle
    cofr
    #
    wbr
    #
    @10
    @11
    wceq
    @5
    cr
    cB
    csn
    cxp
    #
    vx
    cr
    @7
    c1
    cc0
    cif
    #
    cmpt
    #
    cmul
    cof
    co
    #
    @9
    @13
    @5
    @19
    vx
    cr
    cB
    @17
    cmul
    co
    #
    cmpt
    @9
    @5
    vx
    cr
    cB
    @17
    cmul
    @16
    @18
    cvv
    @3
    cr
    cr
    cvv
    wcel
    @5
    reex
    a1i
    #
    @0
    @2
    @4
    @6
    cr
    wcel
    #
    simpl3
    @17
    cr
    wcel
    @5
    @22
    wa
    #
    @7
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    @16
    vx
    cr
    cB
    cmpt
    wceq
    @5
    vx
    cr
    cB
    fconstmpt
    a1i
    @5
    @18
    eqidd
    offval2
    @5
    vx
    cr
    @20
    @8
    @5
    @20
    @7
    cB
    c1
    cmul
    co
    #
    cB
    cc0
    cmul
    co
    #
    cif
    @8
    @7
    cB
    c1
    cc0
    cmul
    ovif2
    @5
    @7
    @24
    cB
    @25
    cc0
    @5
    cB
    @5
    cB
    @5
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    @5
    @4
    @26
    @27
    wa
    @0
    @2
    @4
    simp3
    cB
    elrege0
    sylib
    #
    simpld
    #
    recnd
    #
    mulid1d
    @5
    cB
    @30
    mul01d
    ifeq12d
    syl5eq
    mpteq2dv
    eqtrd
    #
    @5
    cB
    @18
    @0
    @2
    @18
    @13
    wcel
    @4
    vx
    cA
    @18
    @18
    eqid
    #
    i1f1
    3adant3
    #
    @29
    i1fmulc
    eqeltrrd
    @5
    @15
    cc0
    @8
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @5
    @34
    vx
    cr
    @5
    @27
    cc0
    cc0
    cle
    wbr
    #
    @34
    @5
    @26
    @27
    @28
    simprd
    0le0
    @7
    @27
    @36
    @34
    cB
    cc0
    cB
    @8
    cc0
    cle
    breq2
    cc0
    @8
    cc0
    cle
    breq2
    ifboth
    sylancl
    ralrimivw
    @5
    @15
    cr
    cc0
    csn
    cxp
    #
    @9
    @14
    wbr
    @35
    @5
    cr
    @9
    cr
    cc
    wss
    @5
    ax-resscn
    a1i
    @5
    @8
    cr
    wcel
    #
    vx
    cr
    wral
    @9
    cr
    wfn
    @5
    @38
    vx
    cr
    @23
    @26
    cc0
    cr
    wcel
    #
    @38
    @5
    @26
    @22
    @29
    adantr
    0re
    @7
    cB
    cc0
    cr
    ifcl
    sylancl
    #
    ralrimiva
    vx
    cr
    @8
    @9
    cr
    @9
    eqid
    fnmpt
    syl
    0pledm
    @5
    vx
    cr
    cc0
    @8
    cle
    @37
    @9
    cvv
    cr
    cr
    @21
    @39
    @23
    0re
    a1i
    @40
    @37
    vx
    cr
    cc0
    cmpt
    wceq
    @5
    vx
    cr
    cc0
    fconstmpt
    a1i
    @5
    @9
    eqidd
    ofrfval2
    bitrd
    mpbird
    @9
    itg2itg1
    syl2anc
    @5
    @19
    citg1
    cfv
    cB
    @18
    citg1
    cfv
    #
    cmul
    co
    @11
    @12
    @5
    cB
    @18
    @33
    @29
    itg1mulc
    @5
    @19
    @9
    citg1
    @31
    fveq2d
    @5
    @41
    @1
    cB
    cmul
    @0
    @2
    @41
    @1
    wceq
    @4
    vx
    cA
    @18
    @32
    itg11
    3adant3
    oveq2d
    3eqtr3d
    eqtrd
end
