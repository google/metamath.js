include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfm.mm"
include "co.mm"
include "cfcls.mm"
include "cmap.mm"
include "cfcf.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "ctop.mm"
include "crn.mm"
include "cuni.mm"
include "cmpt2.mm"
include "df-fcf.mm"
include "a1i.mm"
include "simprl.mm"
include "unieqd.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "unieq.mm"
include "ad2antll.mm"
include "filunibas.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "simprr.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "topontop.mm"
include "adantr.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "adantl.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2d.mm"
include "3adant3.mm"
include "simpr.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "wb.mm"
include "toponmax.mm"
include "filtop.mm"
include "elmapg.mm"
include "syl2an.mm"
include "biimp3ar.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem fcfval
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  let cS: class S


  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( ( J fClusf L ) ` F ) = ( J fClus ( ( X FilMap F ) ` L ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    vg
    cF
    cJ
    cL
    cX
    vg
    cv
    #
    cfm
    co
    #
    cfv
    #
    cfcls
    co
    #
    cJ
    cL
    cX
    cF
    cfm
    co
    #
    cfv
    #
    cfcls
    co
    cX
    cY
    cmap
    co
    #
    cJ
    cL
    cfcf
    co
    #
    cvv
    @0
    @2
    @12
    vg
    @11
    @8
    cmpt
    #
    wceq
    @3
    @0
    @2
    wa
    #
    vj
    vf
    cJ
    cL
    ctop
    cfil
    crn
    cuni
    #
    vg
    vj
    cv
    #
    cuni
    #
    vf
    cv
    #
    cuni
    #
    cmap
    co
    #
    @16
    @18
    @17
    @5
    cfm
    co
    #
    cfv
    #
    cfcls
    co
    #
    cmpt
    #
    @13
    cfcf
    cvv
    cfcf
    vj
    vf
    ctop
    @15
    @24
    cmpt2
    wceq
    @14
    vf
    vg
    vj
    df-fcf
    a1i
    @14
    @16
    cJ
    wceq
    #
    @18
    cL
    wceq
    #
    wa
    #
    wa
    #
    vg
    @20
    @23
    @11
    @8
    @28
    @17
    cX
    @19
    cY
    cmap
    @28
    @17
    cJ
    cuni
    #
    cX
    @28
    @16
    cJ
    @14
    @25
    @26
    simprl
    #
    unieqd
    @0
    cX
    @29
    wceq
    @2
    @27
    cX
    cJ
    toponuni
    ad2antrr
    eqtr4d
    #
    @28
    @19
    cL
    cuni
    #
    cY
    @26
    @19
    @32
    wceq
    @14
    @25
    @18
    cL
    unieq
    ad2antll
    @2
    @32
    cY
    wceq
    @0
    @27
    cL
    cY
    filunibas
    ad2antlr
    eqtrd
    oveq12d
    @28
    @16
    cJ
    @22
    @7
    cfcls
    @30
    @28
    @18
    cL
    @21
    @6
    @28
    @17
    cX
    @5
    cfm
    @31
    oveq1d
    @14
    @25
    @26
    simprr
    fveq12d
    oveq12d
    mpteq12dv
    @0
    cJ
    ctop
    wcel
    @2
    cX
    cJ
    topontop
    adantr
    @2
    cL
    @15
    wcel
    @0
    @1
    @15
    cL
    cfil
    cY
    fvssunirn
    sseli
    adantl
    @13
    cvv
    wcel
    @14
    vg
    @11
    @8
    cX
    cY
    cmap
    ovex
    mptex
    a1i
    ovmpt2d
    3adant3
    @4
    @5
    cF
    wceq
    #
    wa
    #
    @7
    @10
    cJ
    cfcls
    @34
    cL
    @6
    @9
    @34
    @5
    cF
    cX
    cfm
    @4
    @33
    simpr
    oveq2d
    fveq1d
    oveq2d
    @0
    @2
    cF
    @11
    wcel
    #
    @3
    @0
    cX
    cJ
    wcel
    cY
    cL
    wcel
    @35
    @3
    wb
    @2
    cX
    cJ
    toponmax
    cL
    cY
    filtop
    cX
    cY
    cF
    cJ
    cL
    elmapg
    syl2an
    biimp3ar
    @4
    cJ
    @10
    cfcls
    ovexd
    fvmptd
end
