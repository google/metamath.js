include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cva.mm"
include "wceq.mm"
include "cort.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "chil.mm"
include "csp.mm"
include "cc0.mm"
include "adantr.mm"
include "cheli.mm"
include "ad2antrl.mm"
include "hvsubcl.mm"
include "syl2anc.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "simplrl.mm"
include "simpr.mm"
include "simplrr.mm"
include "eqid.mm"
include "pjhthlem1.mm"
include "ralrimiva.mm"
include "csh.mm"
include "wb.mm"
include "chshii.mm"
include "shocel.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "hvpncan3.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wreu.mm"
include "csm.mm"
include "cop.mm"
include "cxp.mm"
include "cres.mm"
include "cc.mm"
include "df-hba.mm"
include "hhvs.mm"
include "hhnm.mm"
include "hhssba.mm"
include "ccphlo.mm"
include "hhph.mm"
include "a1i.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "hhsst.mm"
include "hhssbn.mm"
include "elin.mm"
include "mpbir2an.mm"
include "minveco.mm"
include "reurex.mm"
include "syl.mm"
include "reximddv.mm"

theorem pjhthlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cT: class T
  assume pjhth.1: |- H e. CH
  assume pjhth.2: |- ( ph -> A e. ~H )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint C x
  disjoint H z
  disjoint T x
  disjoint ph z
  assert |- ( ph -> E. x e. H E. y e. ( _|_ ` H ) A = ( x +h y ) )

  proof
    wph
    cA
    vx
    cv
    #
    cmv
    co
    #
    cno
    cfv
    cA
    vz
    cv
    cmv
    co
    cno
    cfv
    cle
    wbr
    vz
    cH
    wral
    #
    cA
    @0
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cH
    cort
    cfv
    #
    wrex
    #
    vx
    cH
    wph
    @0
    cH
    wcel
    #
    @2
    wa
    #
    wa
    #
    @1
    @6
    wcel
    #
    cA
    @0
    @1
    cva
    co
    #
    wceq
    #
    @7
    @10
    @1
    chil
    wcel
    #
    @1
    @3
    csp
    co
    #
    cc0
    wceq
    #
    vy
    cH
    wral
    #
    @11
    @10
    cA
    chil
    wcel
    #
    @0
    chil
    wcel
    #
    @14
    wph
    @18
    @9
    pjhth.2
    adantr
    #
    @8
    @19
    wph
    @2
    @0
    cH
    pjhth.1
    cheli
    ad2antrl
    #
    cA
    @0
    hvsubcl
    syl2anc
    @10
    @16
    vy
    cH
    @10
    @3
    cH
    wcel
    #
    wa
    vz
    cA
    @0
    @3
    @15
    @3
    @3
    csp
    co
    c1
    caddc
    co
    cdiv
    co
    #
    cH
    pjhth.1
    @10
    @18
    @22
    @20
    adantr
    wph
    @8
    @2
    @22
    simplrl
    @10
    @22
    simpr
    wph
    @8
    @2
    @22
    simplrr
    @23
    eqid
    pjhthlem1
    ralrimiva
    cH
    csh
    wcel
    #
    @11
    @14
    @17
    wa
    wb
    cH
    pjhth.1
    chshii
    #
    vy
    @1
    cH
    shocel
    ax-mp
    sylanbrc
    @10
    @12
    cA
    @10
    @19
    @18
    @12
    cA
    wceq
    @21
    @20
    @0
    cA
    hvpncan3
    syl2anc
    eqcomd
    @5
    @13
    vy
    @1
    @6
    @3
    @1
    wceq
    @4
    @12
    cA
    @3
    @1
    @0
    cva
    oveq2
    eqeq2d
    rspcev
    syl2anc
    wph
    @2
    vx
    cH
    wreu
    @2
    vx
    cH
    wrex
    wph
    vx
    vz
    cA
    cva
    csm
    cop
    cno
    cop
    #
    cmv
    cno
    cva
    cH
    cH
    cxp
    cres
    csm
    cc
    cH
    cxp
    cres
    cop
    cno
    cH
    cres
    cop
    #
    chil
    cH
    df-hba
    @26
    @26
    eqid
    #
    hhvs
    @26
    @28
    hhnm
    cH
    @27
    @27
    eqid
    #
    @25
    hhssba
    @26
    ccphlo
    wcel
    wph
    @26
    @28
    hhph
    a1i
    @27
    @26
    css
    cfv
    #
    ccbn
    cin
    wcel
    #
    wph
    @31
    @27
    @30
    wcel
    #
    @27
    ccbn
    wcel
    @24
    @32
    @25
    @26
    cH
    @27
    @28
    @29
    hhsst
    ax-mp
    cH
    @27
    @29
    pjhth.1
    hhssbn
    @27
    @30
    ccbn
    elin
    mpbir2an
    a1i
    pjhth.2
    minveco
    @2
    vx
    cH
    reurex
    syl
    reximddv
end
