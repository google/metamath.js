include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "ccmp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "icccmplem3.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wb.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "iccssre.mm"
include "adantr.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "cmpsub.mm"
include "sylancr.mm"
include "mpbird.mm"
include "c0.mm"
include "csn.mm"
include "cxr.mm"
include "rexr.mm"
include "icc0.mm"
include "syl2an.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "rest0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0cmp.mm"
include "syl6eqel.mm"
include "lelttric.mm"
include "mpjaodan.mm"
include "syl5eqel.mm"

theorem icccmp
  let cA: class A
  let cB: class B
  let cT: class T
  let cJ: class J
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let wph: wff ph
  let cR: class R
  let cD: class D
  let cG: class G
  let cV: class V
  let cS: class S
  let cU: class U
  assume icccmp.1: |- J = ( topGen ` ran (,) )
  assume icccmp.2: |- T = ( J |`t ( A [,] B ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> T e. Comp )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cT
    cJ
    cA
    cB
    cicc
    co
    #
    crest
    co
    #
    ccmp
    icccmp.2
    @2
    cA
    cB
    cle
    wbr
    #
    @4
    ccmp
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    @2
    @5
    wa
    #
    @6
    @3
    vu
    cv
    #
    cuni
    wss
    #
    @3
    vz
    cv
    cuni
    #
    wss
    #
    vz
    @9
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    cJ
    cpw
    #
    wral
    #
    @8
    @15
    vu
    @16
    @8
    @9
    @16
    wcel
    #
    @10
    @14
    @8
    @18
    @10
    wa
    #
    wa
    #
    cB
    cA
    vx
    cv
    #
    cicc
    co
    #
    @11
    wss
    #
    vz
    @13
    wrex
    #
    vx
    @3
    crab
    #
    wcel
    #
    @14
    @20
    vx
    vz
    cA
    cB
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    @25
    cT
    @9
    cJ
    icccmp.1
    icccmp.2
    @27
    eqid
    @25
    eqid
    @0
    @1
    @5
    @19
    simplll
    @0
    @1
    @5
    @19
    simpllr
    @2
    @5
    @19
    simplr
    @18
    @9
    cJ
    wss
    @8
    @10
    @9
    cJ
    elpwi
    ad2antrl
    @8
    @18
    @10
    simprr
    icccmplem3
    @26
    cB
    @3
    wcel
    @14
    @24
    @14
    vx
    cB
    @3
    @21
    cB
    wceq
    #
    @23
    @12
    vz
    @13
    @28
    @22
    @3
    @11
    @21
    cB
    cA
    cicc
    oveq2
    sseq1d
    rexbidv
    elrab
    simprbi
    syl
    expr
    ralrimiva
    @8
    cJ
    ctop
    wcel
    #
    @3
    cr
    wss
    #
    @6
    @17
    wb
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    icccmp.1
    retop
    eqeltri
    #
    @2
    @30
    @5
    cA
    cB
    iccssre
    adantr
    @3
    cJ
    cr
    vu
    vz
    cr
    @31
    cuni
    cJ
    cuni
    uniretop
    cJ
    @31
    icccmp.1
    unieqi
    eqtr4i
    cmpsub
    sylancr
    mpbird
    @2
    @7
    wa
    #
    @4
    c0
    csn
    #
    ccmp
    @33
    @4
    cJ
    c0
    crest
    co
    #
    @34
    @33
    @3
    c0
    cJ
    crest
    @2
    @3
    c0
    wceq
    #
    @7
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @36
    @7
    wb
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    icc0
    syl2an
    biimpar
    oveq2d
    @29
    @35
    @34
    wceq
    @32
    cJ
    rest0
    ax-mp
    syl6eq
    0cmp
    syl6eqel
    cA
    cB
    lelttric
    mpjaodan
    syl5eqel
end
