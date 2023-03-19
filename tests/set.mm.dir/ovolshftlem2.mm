include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "wf.mm"
include "simplr.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "simpr.mm"
include "ovolshftlem1.mm"
include "eleq1a.mm"
include "syl.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"

theorem ovolshftlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let cM: class M
  let vn: setvar n
  let vw: setvar w
  let vm: setvar m
  let cF: class F
  let cG: class G
  assume ovolshft.1: |- ( ph -> A C_ RR )
  assume ovolshft.2: |- ( ph -> C e. RR )
  assume ovolshft.3: |- ( ph -> B = { x e. RR | ( x - C ) e. A } )
  assume ovolshft.4: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( B C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint B f
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint M g
  disjoint M z
  disjoint f ph
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint f n
  disjoint f w
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint f m
  disjoint g m
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint C n
  disjoint C w
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G n
  disjoint G y
  disjoint B n
  disjoint B w
  disjoint n ph
  disjoint ph w
  assert |- ( ph -> { z e. RR* | E. g e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. g ) /\ z = sup ( ran seq 1 ( + , ( ( abs o. - ) o. g ) ) , RR* , < ) ) } C_ M )

  proof
    wph
    cA
    cioo
    vg
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vz
    cv
    #
    caddc
    cabs
    cmin
    ccom
    @0
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vg
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    #
    @2
    cM
    wcel
    #
    wi
    #
    vz
    cxr
    wral
    @10
    vz
    cxr
    crab
    cM
    wss
    wph
    @12
    vz
    cxr
    wph
    @2
    cxr
    wcel
    #
    wa
    #
    @6
    @11
    vg
    @9
    @14
    @0
    @9
    wcel
    #
    wa
    #
    @1
    @5
    @11
    @16
    @1
    wa
    #
    @4
    cM
    wcel
    @5
    @11
    wi
    @17
    vx
    vy
    cA
    cB
    cC
    @3
    vf
    vn
    @0
    vm
    cn
    vm
    cv
    #
    @0
    cfv
    #
    c1st
    cfv
    #
    cC
    caddc
    co
    #
    @19
    c2nd
    cfv
    #
    cC
    caddc
    co
    #
    cop
    #
    cmpt
    cM
    wph
    cA
    cr
    wss
    @13
    @15
    @1
    ovolshft.1
    ad3antrrr
    wph
    cC
    cr
    wcel
    @13
    @15
    @1
    ovolshft.2
    ad3antrrr
    wph
    cB
    vx
    cv
    cC
    cmin
    co
    cA
    wcel
    vx
    cr
    crab
    wceq
    @13
    @15
    @1
    ovolshft.3
    ad3antrrr
    ovolshft.4
    @3
    eqid
    vm
    vn
    cn
    @24
    vn
    cv
    #
    @0
    cfv
    #
    c1st
    cfv
    #
    cC
    caddc
    co
    #
    @26
    c2nd
    cfv
    #
    cC
    caddc
    co
    #
    cop
    @18
    @25
    wceq
    #
    @21
    @28
    @23
    @30
    @31
    @20
    @27
    cC
    caddc
    @31
    @19
    @26
    c1st
    @18
    @25
    @0
    fveq2
    #
    fveq2d
    oveq1d
    @31
    @22
    @29
    cC
    caddc
    @31
    @19
    @26
    c2nd
    @32
    fveq2d
    oveq1d
    opeq12d
    cbvmptv
    @17
    @15
    cn
    @8
    @0
    wf
    @14
    @15
    @1
    simplr
    @8
    cn
    @0
    @7
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    sylib
    @16
    @1
    simpr
    ovolshftlem1
    @4
    cM
    @2
    eleq1a
    syl
    expimpd
    rexlimdva
    ralrimiva
    @10
    vz
    cxr
    cM
    rabss
    sylibr
end
